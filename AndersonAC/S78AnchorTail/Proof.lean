import AndersonAC.S78AnchorTail.Geometry
import AndersonAC.S78.AssemblyEstimates

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78AnchorTail

open AndersonAC.S78 AndersonAC.SolS78

private theorem outside_cube_distance_lower {d m : ℕ} (x z : Torus d m) (R : ℝ)
    (hx : x ∉ cube d m z R) : R < physicalDistance d m x z := by
  classical
  have hnot : ¬ ∀ q : Fin d,
      ((min ((x q - z q).val) (OAI.Anderson.sideLength m - (x q - z q).val) : ℕ) : ℝ) ≤ R := by
    simpa [cube] using hx
  push_neg at hnot
  obtain ⟨q, hq⟩ := hnot
  have hq' : R <
      ((min ((x q - z q).val) (OAI.Anderson.sideLength m - (x q - z q).val) : ℕ) : ℝ) := hq
  exact lt_of_lt_of_le hq' (coordNat_le_physicalDistance q x z)

private theorem distanceTo_removed_lower_bound {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) (a : Fin k)
    (x : Torus d m) :
    physicalDistance d m x (I.anchor a) - I.Ds ≤
      distanceTo (physicalDistance d m)
        ((I.state a.castSucc).active \ (I.state a.succ).active) x := by
  classical
  let O := (I.state a.castSucc).active \ (I.state a.succ).active
  have hO : O.Nonempty := I.removedNonempty a
  unfold distanceTo
  apply le_csInf
  · obtain ⟨z, hz⟩ := hO
    exact ⟨physicalDistance d m x z, z, hz, rfl⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    have htri := physicalDistance_triangle d m x z (I.anchor a)
    have hlocal := I.removedLocal a z hz
    linarith

private theorem scalar_cutoff_le_ds {d m k : ℕ} {t C : ℝ}
    {b : ℝ} {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) (hC : 1 ≤ C)
    (htpos : 0 < t) (htle : t ≤ 1) (ht₀ : t < (C + 1)⁻¹) :
    C * t ^ (-1.03 : ℝ) ≤ I.Ds := by
  have hCplus : 0 < C + 1 := by linarith
  have hmul : t * (C + 1) < 1 := by
    apply (lt_div_iff₀ hCplus).1
    simpa [one_div] using ht₀
  have hCinv : C ≤ t ^ (-1 : ℝ) := by
    have hCdiv : C ≤ 1 / t :=
      (le_div_iff₀ htpos).2 (by nlinarith [hmul, htpos, hC])
    simpa [Real.rpow_neg_one] using hCdiv
  have hpow : t ^ (-1.03 : ℝ) ≤ t ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle (by norm_num)
  have hprod : C * t ^ (-1.03 : ℝ) ≤ t ^ (-3 : ℝ) := by
    calc
      C * t ^ (-1.03 : ℝ) ≤ t ^ (-1 : ℝ) * t ^ (-2 : ℝ) :=
        mul_le_mul hCinv hpow (by positivity) (by positivity)
      _ = t ^ (-3 : ℝ) := by
        rw [← Real.rpow_add htpos]
        norm_num
  have hpow38 : t ^ (-3 : ℝ) ≤ t ^ (-8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle (by norm_num)
  have hnu : 0 ≤ nu d := by
    unfold nu delta
    positivity
  have hpow8 : t ^ (-8 : ℝ) ≤ t ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle (by linarith)
  have hDs : t ^ (-8 : ℝ) ≤ I.Ds := hpow8.trans I.scaleRadius.1
  exact hprod.trans (hpow38.trans hDs)

private theorem max_sum_lower (x y k : ℝ) :
    x + y - 2 * k ≤ max (x - k) 0 + max (y - k) 0 := by
  have hx := le_max_left (x - k) 0
  have hy := le_max_left (y - k) 0
  linarith

theorem assemblyAnchorTailInput_proof : AssemblyAnchorTailInput := by
  intro d hd C c P hC hc hP
  refine ⟨P, (C + 1)⁻¹, hP, by positivity, ?_⟩
  intro m k t b r I hIC hIc hIP ht₀ a i j hout
  rcases I.positive with ⟨htpos, htle, _, _, _, _, _⟩
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hpow8 : t ^ (-8 : ℝ) ≤ t ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle (by linarith)
  have hDs8 : t ^ (-8 : ℝ) ≤ I.Ds := hpow8.trans I.scaleRadius.1
  have hcutC : C * t ^ (-1.03 : ℝ) ≤ I.Ds :=
    scalar_cutoff_le_ds I hC htpos htle ht₀
  have hcut : I.C * t ^ (-1.03 : ℝ) ≤ I.Ds := by simpa [hIC] using hcutC
  have hDnonneg : 0 ≤ I.Ds := le_of_lt (lt_of_lt_of_le (by positivity : 0 < t ^ (-8 : ℝ)) hDs8)
  let O := (I.state a.castSucc).active \ (I.state a.succ).active
  let ρi := physicalDistance d m i (I.anchor a)
  let ρj := physicalDistance d m j (I.anchor a)
  let σi := distanceTo (physicalDistance d m) O i
  let σj := distanceTo (physicalDistance d m) O j
  let K := I.C * t ^ (-1.03 : ℝ)
  let S := max (σi - K) 0 + max (σj - K) 0
  have hρi : 0 ≤ ρi := by dsimp [ρi, physicalDistance]; positivity
  have hρj : 0 ≤ ρj := by dsimp [ρj, physicalDistance]; positivity
  have hρsum : 100 * I.Ds ≤ ρi + ρj := by
    rcases hout with hi | hj
    · have hfar := outside_cube_distance_lower i (I.anchor a) (100 * I.Ds) hi
      linarith
    · have hfar := outside_cube_distance_lower j (I.anchor a) (100 * I.Ds) hj
      linarith
  have hσi : ρi - I.Ds ≤ σi := by
    simpa [ρi, σi, O] using distanceTo_removed_lower_bound I a i
  have hσj : ρj - I.Ds ≤ σj := by
    simpa [ρj, σj, O] using distanceTo_removed_lower_bound I a j
  have hσsum : ρi + ρj - 2 * I.Ds ≤ σi + σj := by linarith
  have hS0 : σi + σj - 2 * K ≤ S := by
    dsimp [S]
    exact max_sum_lower σi σj K
  have hK : K ≤ I.Ds := by dsimp [K]; exact hcut
  have hS : ρi + ρj - 4 * I.Ds ≤ S := by nlinarith [hσsum, hS0, hK]
  have hSquarter : (I.Ds + (ρi + ρj)) / 4 ≤ S := by
    have hD' : 0 ≤ I.Ds := hDnonneg
    nlinarith [hρsum, hS, hD']
  have harg : -c * t * S ≤ -(c / 4) * t * (I.Ds + (ρi + ρj)) := by
    have hct : 0 ≤ c * t := mul_nonneg hc.le htpos.le
    have hmul := mul_le_mul_of_nonneg_left hSquarter hct
    nlinarith
  have hdec :
      ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t i j‖ ≤
        t ^ (-P : ℝ) * Real.exp (-c * t * S) := by
    simpa [S, σi, σj, K, O, hIC, hIc, hIP] using I.decay a i j
  have hexp : Real.exp (-c * t * S) ≤
      Real.exp (-(c / 4) * t * (I.Ds + (ρi + ρj))) :=
    Real.exp_le_exp.mpr harg
  have hsplit : Real.exp (-(c / 4) * t * (I.Ds + (ρi + ρj))) =
      Real.exp (-(c / 4) * t * I.Ds) * Real.exp (-(c / 4) * t * (ρi + ρj)) := by
    rw [show -(c / 4) * t * (I.Ds + (ρi + ρj)) =
      (-(c / 4) * t * I.Ds) + (-(c / 4) * t * (ρi + ρj)) by ring, Real.exp_add]
  calc
    ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t i j‖ ≤
        t ^ (-P : ℝ) * Real.exp (-c * t * S) := hdec
    _ ≤ t ^ (-P : ℝ) * Real.exp (-(c / 4) * t * (I.Ds + (ρi + ρj))) :=
      mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.rpow_pos_of_pos htpos _))
    _ = t ^ (-P : ℝ) * Real.exp (-(c / 4) * t * I.Ds) *
        Real.exp (-(c / 4) * t * (ρi + ρj)) := by rw [hsplit]; ring

end AndersonAC.SolS78AnchorTail

namespace AndersonAC.SolS78

theorem assemblyAnchorTailInput_proof : AssemblyAnchorTailInput :=
  AndersonAC.SolS78AnchorTail.assemblyAnchorTailInput_proof

end AndersonAC.SolS78
