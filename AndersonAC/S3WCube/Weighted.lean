import AndersonAC.S3WCube.Reflect

/-! Lemma 3.3 (`eq:initial-weighted-cube`): the weighted cube Poincaré estimate. -/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AndersonAC.AgentS3
open AndersonAC.S3

lemma rpow_third_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

lemma gradientEnergy_nonneg {d L : ℕ} [NeZero L] (v : Torus d L → ℂ) :
    0 ≤ gradientEnergy v := by
  unfold gradientEnergy
  positivity

lemma centered_eq_zero_of_one {d : ℕ} (v : Cube d 1 → ℂ) (i : Cube d 1) :
    v i - cubeMean v = 0 := by
  have hcard : Fintype.card (Cube d 1) = 1 := by simp
  have hsum : (∑ j, v j) = v i := Fintype.sum_subsingleton _ i
  unfold cubeMean
  rw [hcard, hsum]
  simp

/-- The weighted conjunct on the reflected torus, after the Fourier split. -/
lemma weighted_reflected_bound {d l : ℕ} (hd : 3 ≤ d) {C1 : ℝ}
    (hLow : ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (v : Torus d L → ℂ), neutral v →
        ∀ x : Torus d L,
          ∃ S : Finset (Torus d L),
            S = Finset.univ.filter (fun k =>
              1 ≤ torusDistance (0 : Torus d L) k ∧
                torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊) ∧
            ‖fourierBandPart S v x‖ ^ 2 ≤ C1 * a * gradientEnergy v)
    (hl : 2 ≤ l) [NeZero (2 * l)] (v : Cube d l → ℂ) (w : Cube d l → ℝ)
    (hw : ∀ i, 0 ≤ w i) (M a : ℝ) (hwM : ∀ i, w i ≤ M) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∑ i, w i * ‖v i - cubeMean v‖ ^ 2) ≤
      (2 * C1 * a * (∑ i, w i) + 2 * M * ((d : ℝ) / (16 * a ^ 2))) *
        gradientEnergy (reflected (by omega : 0 < l) v) := by
  have hl0 : 0 < l := by omega
  have hL : 4 ≤ 2 * l := by omega
  set u := reflected hl0 v
  set E := gradientEnergy u
  have hu : neutral u := reflected_neutral hl0 v
  set Sset : Finset (Torus d (2 * l)) := Finset.univ.filter (fun k =>
      1 ≤ torusDistance (0 : Torus d (2 * l)) k ∧
        torusDistance (0 : Torus d (2 * l)) k ≤ ⌊a * ((2 * l : ℕ) : ℝ)⌋₊)
  set P := fourierBandPart Sset u
  set Q := fourierBandComplement Sset u
  have hdec : ∀ x, u x = P x + Q x := by
    intro x
    rw [fourierBandPart_add_complement, synthesis_fourier]
  have hP : ∀ x, ‖P x‖ ^ 2 ≤ C1 * a * E := by
    intro x
    obtain ⟨S', hS', hb⟩ := hLow (2 * l) hL a ha0 ha1 u hu x
    rw [hS'] at hb
    exact hb
  have hQ : normSq Q ≤ (d : ℝ) / (16 * a ^ 2) * E := by
    obtain ⟨S', hS', hb⟩ := fourier_high_part_energy_bound hd (2 * l) hL a ha0 ha1 u hu
    rw [hS'] at hb
    exact hb
  have hterm : ∀ i, w i * ‖v i - cubeMean v‖ ^ 2 ≤
      2 * C1 * a * E * w i + 2 * M * ‖Q (cubeEmbed i)‖ ^ 2 := by
    intro i
    have h1 : v i - cubeMean v = P (cubeEmbed i) + Q (cubeEmbed i) := by
      rw [← reflected_cubeEmbed hl0 v i]
      exact hdec _
    rw [h1]
    have h2 := norm_add_sq_le_two (P (cubeEmbed i)) (Q (cubeEmbed i))
    have h3 := hP (cubeEmbed i)
    have hwi := hw i
    have hwMi := hwM i
    have hq := sq_nonneg ‖Q (cubeEmbed i)‖
    have hp := sq_nonneg ‖P (cubeEmbed i)‖
    calc w i * ‖P (cubeEmbed i) + Q (cubeEmbed i)‖ ^ 2
        ≤ w i * (2 * ‖P (cubeEmbed i)‖ ^ 2 + 2 * ‖Q (cubeEmbed i)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hwi
      _ = 2 * (w i * ‖P (cubeEmbed i)‖ ^ 2) + 2 * (w i * ‖Q (cubeEmbed i)‖ ^ 2) := by ring
      _ ≤ 2 * (w i * (C1 * a * E)) + 2 * (M * ‖Q (cubeEmbed i)‖ ^ 2) := by
          gcongr
      _ = 2 * C1 * a * E * w i + 2 * M * ‖Q (cubeEmbed i)‖ ^ 2 := by ring
  have hM0 : 0 ≤ M := by
    have := hwM (fun _ => ⟨0, hl0⟩)
    exact (hw _).trans this
  have hQembed : (∑ i : Cube d l, ‖Q (cubeEmbed i)‖ ^ 2) ≤ normSq Q :=
    sum_cubeEmbed_le (fun x => ‖Q x‖ ^ 2) (fun _ => sq_nonneg _)
  calc (∑ i, w i * ‖v i - cubeMean v‖ ^ 2)
      ≤ ∑ i, (2 * C1 * a * E * w i + 2 * M * ‖Q (cubeEmbed i)‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 * C1 * a * E * (∑ i, w i) + 2 * M * (∑ i, ‖Q (cubeEmbed i)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * C1 * a * E * (∑ i, w i) + 2 * M * ((d : ℝ) / (16 * a ^ 2) * E) := by
        gcongr
        exact hQembed.trans hQ
    _ = (2 * C1 * a * (∑ i, w i) + 2 * M * ((d : ℝ) / (16 * a ^ 2))) * E := by ring

theorem weighted_cube_proof {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ), 1 ≤ l → ∀ (v : Cube d l → ℂ) (w : Cube d l → ℝ),
      (∀ i, 0 ≤ w i) →
      normSq (fun i => v i - cubeMean v) ≤ C * (l : ℝ) ^ 2 * cubeEnergy v ∧
      (∑ i, w i * ‖v i - cubeMean v‖ ^ 2) ≤
        C * Real.rpow (sSup (Set.range w)) (1 / 3) *
          Real.rpow (∑ i, w i) (2 / 3) * cubeEnergy v := by
  obtain ⟨C0, hC0, hPoin⟩ := torus_poincare_proof (d := d) hd
  obtain ⟨C1, hC1, hLow⟩ := fourier_low_part_pointwise_bound (d := d) hd
  set B : ℝ := (2 : ℝ) ^ (d + 1)
  have hB : 0 < B := by positivity
  set CA : ℝ := C0 * 4 * B
  set CB : ℝ := (2 * C1 + (d : ℝ) / 8) * B
  have hCA : 0 < CA := by positivity
  have hCB : 0 < CB := by positivity
  refine ⟨CA + CB, by positivity, ?_⟩
  intro l hl1 v w hw
  have hl0 : 0 < l := by omega
  set M : ℝ := sSup (Set.range w)
  set S : ℝ := ∑ i, w i
  have hcE := cubeEnergy_nonneg v
  have hwM : ∀ i, w i ≤ M := fun i =>
    le_csSup (Set.finite_range w).bddAbove ⟨i, rfl⟩
  have hM0 : 0 ≤ M := (hw (fun _ => ⟨0, hl0⟩)).trans (hwM _)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hw i)
  have hrhs1 : 0 ≤ (CA + CB) * (l : ℝ) ^ 2 * cubeEnergy v := by positivity
  have hrhs2 : 0 ≤ (CA + CB) * Real.rpow M (1 / 3) * Real.rpow S (2 / 3) * cubeEnergy v := by
    have h1 : 0 ≤ Real.rpow M (1 / 3) := Real.rpow_nonneg hM0 _
    have h2 : 0 ≤ Real.rpow S (2 / 3) := Real.rpow_nonneg hS0 _
    positivity
  -- The one-point cube.
  rcases Nat.lt_or_ge l 2 with hlt | hl2
  · have hl : l = 1 := by omega
    subst hl
    have hz : ∀ i, v i - cubeMean v = 0 := centered_eq_zero_of_one v
    refine ⟨?_, ?_⟩
    · have : normSq (fun i => v i - cubeMean v) = 0 := by
        unfold normSq
        simp [hz]
      rw [this]
      exact hrhs1
    · have : (∑ i, w i * ‖v i - cubeMean v‖ ^ 2) = 0 := by simp [hz]
      rw [this]
      exact hrhs2
  have : NeZero (2 * l) := ⟨by omega⟩
  have hL : 4 ≤ 2 * l := by omega
  set u := reflected hl0 v
  set E := gradientEnergy u
  have hE0 : 0 ≤ E := gradientEnergy_nonneg u
  have hEc : E ≤ B * cubeEnergy v := reflected_gradientEnergy_le hl0 v
  refine ⟨?_, ?_⟩
  · -- Unweighted conjunct.
    have h1 : normSq (fun i => v i - cubeMean v) ≤ normSq u := by
      have := sum_cubeEmbed_le (l := l) (fun x => ‖u x‖ ^ 2) (fun _ => sq_nonneg _)
      unfold normSq
      simpa [u, reflected_cubeEmbed hl0 v] using this
    have h2 := hPoin (2 * l) hL u (reflected_neutral hl0 v)
    have hcast : ((2 * l : ℕ) : ℝ) = 2 * (l : ℝ) := by push_cast; ring
    rw [hcast] at h2
    have hl2' : (0 : ℝ) ≤ (l : ℝ) ^ 2 := by positivity
    calc normSq (fun i => v i - cubeMean v)
        ≤ C0 * (2 * (l : ℝ)) ^ 2 * E := h1.trans h2
      _ = C0 * 4 * (l : ℝ) ^ 2 * E := by ring
      _ ≤ C0 * 4 * (l : ℝ) ^ 2 * (B * cubeEnergy v) := by gcongr
      _ = CA * (l : ℝ) ^ 2 * cubeEnergy v := by ring
      _ ≤ (CA + CB) * (l : ℝ) ^ 2 * cubeEnergy v := by
          have : 0 ≤ CB * (l : ℝ) ^ 2 * cubeEnergy v := by positivity
          nlinarith
  · -- Weighted conjunct.
    rcases eq_or_lt_of_le hS0 with hS | hSpos
    · have hw0 : ∀ i, w i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp hS.symm i
          (Finset.mem_univ i)
      have : (∑ i, w i * ‖v i - cubeMean v‖ ^ 2) = 0 := by simp [hw0]
      rw [this]
      exact hrhs2
    have hMpos : 0 < M := by
      rcases eq_or_lt_of_le hM0 with hM | hM
      · exfalso
        have hw0 : ∀ i, w i = 0 := fun i => le_antisymm (hM ▸ hwM i) (hw i)
        have : S = 0 := by simp [S, hw0]
        linarith
      · exact hM
    have hMS : M ≤ S := by
      have : Nonempty (Cube d l) := ⟨fun _ => ⟨0, hl0⟩⟩
      apply csSup_le (Set.range_nonempty w)
      rintro _ ⟨i, rfl⟩
      exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
    set p : ℝ := M ^ (1 / 3 : ℝ)
    set q : ℝ := S ^ (1 / 3 : ℝ)
    have hp : 0 < p := Real.rpow_pos_of_pos hMpos _
    have hq : 0 < q := Real.rpow_pos_of_pos hSpos _
    have hp3 : p ^ 3 = M := rpow_third_pow_three hM0
    have hq3 : q ^ 3 = S := rpow_third_pow_three hS0
    set a : ℝ := (M / S) ^ (1 / 3 : ℝ)
    have ha : a = p / q := Real.div_rpow hM0 hS0 _
    have ha0 : 0 < a := by rw [ha]; positivity
    have ha1 : a ≤ 1 :=
      Real.rpow_le_one (div_nonneg hM0 hS0) ((div_le_one hSpos).mpr hMS) (by norm_num)
    have hmain := weighted_reflected_bound hd hLow hl2 v w hw M a hwM ha0 ha1
    have hRHS : Real.rpow M (1 / 3) * Real.rpow S (2 / 3) = p * q ^ 2 := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow, rpow_two_thirds_eq hS0]
    have hcoef : 2 * C1 * a * S + 2 * M * ((d : ℝ) / (16 * a ^ 2)) =
        (2 * C1 + (d : ℝ) / 8) * (p * q ^ 2) := by
      rw [ha, ← hp3, ← hq3]
      field_simp
      ring
    rw [hcoef] at hmain
    have hK : 0 ≤ p * q ^ 2 := by positivity
    calc (∑ i, w i * ‖v i - cubeMean v‖ ^ 2)
        ≤ (2 * C1 + (d : ℝ) / 8) * (p * q ^ 2) * E := hmain
      _ ≤ (2 * C1 + (d : ℝ) / 8) * (p * q ^ 2) * (B * cubeEnergy v) := by gcongr
      _ = CB * (p * q ^ 2) * cubeEnergy v := by ring
      _ ≤ (CA + CB) * (p * q ^ 2) * cubeEnergy v := by
          have : 0 ≤ CA * (p * q ^ 2) * cubeEnergy v := by positivity
          nlinarith
      _ = (CA + CB) * Real.rpow M (1 / 3) * Real.rpow S (2 / 3) * cubeEnergy v := by
          rw [mul_assoc (CA + CB) (Real.rpow M (1 / 3)), hRHS]

end AndersonAC.AgentS3
