import AndersonAC.S9Inf.ResidualReadout
import AndersonAC.S9Inf.ComparisonStatement

/-! Uniform comparison from one infinite CT factor and a finite boundary layer. -/

noncomputable section

open OAI.Anderson AndersonAC.S9 AndersonAC.SolS9 Filter

namespace AndersonAC.SolS9Inf

theorem root_cube_scale (m : ℕ) (hm : 1 ≤ m) :
    4 * (sideLength m / 4) = sideLength m ∧
      2 * (sideLength m / 4) + 3 ≤ sideLength m := by
  have he : 20 * m = (20 * m - 1) + 1 := by omega
  have hpow : sideLength m = 4 ^ (20 * m - 1) * 4 := by
    change 4 ^ (20 * m) = _
    conv_lhs => rw [he, pow_succ]
  have hdiv : 4 ∣ sideLength m := ⟨4 ^ (20 * m - 1), by rw [hpow]; ring⟩
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp := Nat.mod_add_div (sideLength m) 4
  have hL : 16 ≤ sideLength m := by
    change 4 ^ 2 ≤ 4 ^ (20 * m)
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  omega

theorem finite_infinite_comparison_of_shell (hshell : LatticeCubeShellStatement) :
    FiniteInfiniteComparisonStatement := by
  intro d hd coupling
  have hd0 : 0 < d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨C₀, c₀, hC₀, hc₀, hCT⟩ := combes_thomas_infinite_proof d coupling
  refine ⟨8 * (d : ℝ) ^ 2 * C₀, c₀ / 4, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  intro E η hη ωm ω hmatch
  have hηp : 0 < η := hη.1
  let R := sideLength m / 4
  obtain ⟨S, hS, hcard, hdist⟩ := hshell d hd0 R
  let r := columnResidual R coupling ω ((E : ℂ) + η * Complex.I)
    (fun q => matrixResolvent (periodicHamiltonian coupling ωm) E η q 0)
  have hs : ∀ x, x ∉ S → r x = 0 := by
    intro x hx
    apply columnResidual_support coupling E η hη.1 ωm ω hmatch x
    intro h
    exact hx ((hS x).mpr h)
  have hr : ∀ x ∈ S, ‖r x‖ ≤ 2 * (d : ℝ) * η⁻¹ := by
    intro x _
    exact actual_columnResidual_norm_le coupling E η hη.1 ωm ω hmatch x
  have hgreen : ∀ x ∈ S,
      ‖scalarGreen coupling ω 0 x ((E : ℂ) + η * Complex.I)‖ ≤
        C₀ / η * Real.exp (-c₀ * η * (R : ℝ)) := by
    intro x hx
    apply (hCT E η hη ω 0 x).trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hC₀.le hη.1.le)
    apply Real.exp_le_exp.mpr
    have hdist' : (R : ℝ) ≤ latticeDistance 0 x := by exact_mod_cast hdist x hx
    exact mul_le_mul_of_nonpos_left hdist' (by nlinarith : -c₀ * η ≤ 0)
  obtain ⟨hscale, houter⟩ := root_cube_scale m hm
  have hcountNat : S.card ≤ 4 * d * (sideLength m) ^ (d - 1) :=
    hcard.trans (by dsimp [R]; gcongr)
  have hcount : (S.card : ℝ) ≤ 4 * (d : ℝ) * (sideLength m : ℝ) ^ (d - 1) := by
    exact_mod_cast hcountNat
  have hR : (R : ℝ) = (sideLength m : ℝ) / 4 := by
    have hreal : 4 * (R : ℝ) = (sideLength m : ℝ) := by exact_mod_cast hscale
    linarith
  change ‖matrixResolvent (periodicHamiltonian coupling ωm) E η 0 0 -
    diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)‖ ≤ _
  rw [root_difference_residual coupling E η hη.1 ωm ω]
  calc
    _ ≤ (S.card : ℝ) * (C₀ / η * Real.exp (-c₀ * η * (R : ℝ))) *
        (2 * (d : ℝ) * η⁻¹) :=
      residual_root_bound coupling ω _ r S hs _ _ (by positivity) (by positivity) hgreen hr
    _ ≤ (4 * (d : ℝ) * (sideLength m : ℝ) ^ (d - 1)) *
        (C₀ / η * Real.exp (-c₀ * η * (R : ℝ))) * (2 * (d : ℝ) * η⁻¹) := by
      gcongr
    _ = _ := by
      rw [hR]
      have hexp : -c₀ * η * ((sideLength m : ℝ) / 4) =
          -(c₀ / 4) * η * (sideLength m : ℝ) := by ring
      rw [hexp, div_eq_mul_inv]
      ring

end AndersonAC.SolS9Inf
