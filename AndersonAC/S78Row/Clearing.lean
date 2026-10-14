import AndersonAC.S78.Definitions

open scoped BigOperators
open AndersonAC.S78
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

theorem successful_clearing_distortions_proof (d : ℕ) (hd : 3 ≤ d)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧ ∀ (ι : Type) [Fintype ι]
      (heat core : Matrix ι ι ℂ) (t : ℝ), 0 < t → t < min t₀ 1 →
      (∀ i j, ‖heat i j‖ ≤ Real.sqrt t * t ^ (0.42 * delta)) →
      (∀ i, rowTwo heat i ≤ t ^ (0.25 * delta)) →
      frobeniusSq heat ≤ t ^ (-1 - 0.47 * delta) →
      (∀ i j, ‖core i j‖ ≤ C * Real.sqrt t * t ^ (0.44 * delta)) →
      (∀ i, rowTwo core i ≤ C * t ^ (0.44 * delta)) →
      frobeniusSq core ≤ C * t ^ (-1 - nu d) →
      (∀ i j, ‖(heat + core) i j‖ ≤ C' * Real.sqrt t * t ^ (0.42 * delta)) ∧
      (∀ i, rowTwo (heat + core) i ≤ C' * t ^ (0.25 * delta)) ∧
      frobeniusSq (heat + core) ≤ C' * t ^ (-1 - 0.47 * delta) := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnuSmall : nu d ≤ (1 : ℝ) / 100000 := by
    rw [nu, delta]
    rw [div_le_iff₀ (by positivity : 0 < (100000 : ℝ) * (d : ℝ))]
    norm_num
    nlinarith
  have hnuBound : nu d ≤ (0.47 : ℝ) * delta := by
    calc
      nu d ≤ (1 : ℝ) / 100000 := hnuSmall
      _ ≤ (0.47 : ℝ) * delta := by norm_num [delta]
  have h42to44 : (0.42 : ℝ) * delta ≤ (0.44 : ℝ) * delta := by
    norm_num [delta]
  have h25to44 : (0.25 : ℝ) * delta ≤ (0.44 : ℝ) * delta := by
    norm_num [delta]
  let K : ℝ := 2 * (C + 1)
  have hKpos : 0 < K := by dsimp [K]; nlinarith
  have hcoeff : 1 + C ≤ K := by dsimp [K]; nlinarith
  have hsqadd (x y : ℂ) :
      ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hnorm := norm_add_le x y
    have hprod := mul_nonneg
      (sub_nonneg.mpr hnorm)
      (add_nonneg (norm_nonneg (x + y))
        (add_nonneg (norm_nonneg x) (norm_nonneg y)))
    have hdiag := sq_nonneg (‖x‖ - ‖y‖)
    nlinarith
  have hrowAdd {ι : Type} [Fintype ι]
      (heat core : Matrix ι ι ℂ) (i : ι) :
      rowTwo (heat + core) i ≤ 2 * rowTwo heat i + 2 * rowTwo core i := by
    classical
    unfold rowTwo
    calc
      (∑ j, ‖(heat + core) i j‖ ^ 2) ≤
          ∑ j, (2 * ‖heat i j‖ ^ 2 + 2 * ‖core i j‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact hsqadd (heat i j) (core i j)
      _ = 2 * rowTwo heat i + 2 * rowTwo core i := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, rowTwo]
  have hfrobeniusAdd {ι : Type} [Fintype ι]
      (heat core : Matrix ι ι ℂ) :
      frobeniusSq (heat + core) ≤ 2 * frobeniusSq heat + 2 * frobeniusSq core := by
    classical
    unfold frobeniusSq
    calc
      (∑ i, rowTwo (heat + core) i) ≤
          ∑ i, (2 * rowTwo heat i + 2 * rowTwo core i) := by
        apply Finset.sum_le_sum
        intro i _
        exact hrowAdd heat core i
      _ = 2 * frobeniusSq heat + 2 * frobeniusSq core := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, frobeniusSq]
  refine ⟨K, 1, hKpos, by norm_num, ?_⟩
  intro ι _ heat core t ht htmin hheatEntry hheatRow hheatFrob
    hcoreEntry hcoreRow hcoreFrob
  have htlt : t < 1 := lt_of_lt_of_le htmin (min_le_right _ _)
  have htle : t ≤ 1 := htlt.le
  have hpow42 : t ^ ((0.44 : ℝ) * delta) ≤ t ^ ((0.42 : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_ge ht htle h42to44
  have hpow25 : t ^ ((0.44 : ℝ) * delta) ≤ t ^ ((0.25 : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_ge ht htle h25to44
  have hpowFrob : t ^ (-1 - nu d) ≤ t ^ (-1 - (0.47 : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_ge ht htle (by linarith)
  have hcoreRowSmall (i : ι) : rowTwo core i ≤ C * t ^ ((0.25 : ℝ) * delta) := by
    exact (hcoreRow i).trans (mul_le_mul_of_nonneg_left hpow25 hC0)
  have hcoreFrobSmall : frobeniusSq core ≤ C * t ^ (-1 - (0.47 : ℝ) * delta) := by
    exact hcoreFrob.trans (mul_le_mul_of_nonneg_left hpowFrob hC0)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hcoreEntrySmall :
        ‖core i j‖ ≤ C * Real.sqrt t * t ^ ((0.42 : ℝ) * delta) := by
      exact (hcoreEntry i j).trans
        (mul_le_mul_of_nonneg_left hpow42
          (mul_nonneg hC0 (Real.sqrt_nonneg t)))
    have hbaseNonneg : 0 ≤ Real.sqrt t * t ^ ((0.42 : ℝ) * delta) :=
      mul_nonneg (Real.sqrt_nonneg t) (Real.rpow_pos_of_pos ht _).le
    calc
      ‖(heat + core) i j‖ ≤ ‖heat i j‖ + ‖core i j‖ := norm_add_le _ _
      _ ≤ Real.sqrt t * t ^ ((0.42 : ℝ) * delta) +
          C * Real.sqrt t * t ^ ((0.42 : ℝ) * delta) :=
        add_le_add (hheatEntry i j) hcoreEntrySmall
      _ = (1 + C) * (Real.sqrt t * t ^ ((0.42 : ℝ) * delta)) := by ring
      _ ≤ K * (Real.sqrt t * t ^ ((0.42 : ℝ) * delta)) :=
        mul_le_mul_of_nonneg_right hcoeff hbaseNonneg
      _ = K * Real.sqrt t * t ^ ((0.42 : ℝ) * delta) := by ring
  · intro i
    calc
      rowTwo (heat + core) i ≤ 2 * rowTwo heat i + 2 * rowTwo core i :=
        hrowAdd heat core i
      _ ≤ 2 * t ^ ((0.25 : ℝ) * delta) +
          2 * (C * t ^ ((0.25 : ℝ) * delta)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hheatRow i) (by norm_num))
          (mul_le_mul_of_nonneg_left (hcoreRowSmall i) (by norm_num))
      _ = K * t ^ ((0.25 : ℝ) * delta) := by dsimp [K]; ring
  · calc
      frobeniusSq (heat + core) ≤
          2 * frobeniusSq heat + 2 * frobeniusSq core :=
        hfrobeniusAdd heat core
      _ ≤ 2 * t ^ (-1 - (0.47 : ℝ) * delta) +
          2 * (C * t ^ (-1 - (0.47 : ℝ) * delta)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hheatFrob (by norm_num))
          (mul_le_mul_of_nonneg_left hcoreFrobSmall (by norm_num))
      _ = K * t ^ (-1 - (0.47 : ℝ) * delta) := by dsimp [K]; ring

end AndersonAC.SolS78
