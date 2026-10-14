import AndersonAC.S78MatrixBounds.AnchorSums
import AndersonAC.S78.AssemblyEstimates

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

private theorem cube_hundred_subset_twohundred (d m : ℕ) (z : Torus d m) (R : ℝ)
    (hR : 0 ≤ R) :
    cube d m z (100 * R) ⊆ cube d m z (200 * R) := by
  classical
  intro x hx
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro q
  calc
    ((min ((x q - z q).val) (OAI.Anderson.sideLength m - (x q - z q).val) : ℕ) : ℝ) ≤
        100 * R := hx q
    _ ≤ 200 * R := by nlinarith

/-- Only the halo-overlap number of operations can be near a fixed site. -/
theorem assembly_near_operation_count {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) (i : Torus d m) :
    ((Finset.univ.filter (fun a : Fin k =>
        i ∈ cube d m (I.anchor a) (100 * I.Ds))).card : ℝ) ≤
      I.C * t ^ (-(d : ℝ) * nu d) := by
  classical
  rcases I.positive with ⟨ht, ht1, hb, hbt, hc, hC, hP⟩
  have hDs : 0 ≤ I.Ds := by
    have hpow : 0 < t ^ (-8 - nu d) := Real.rpow_pos_of_pos ht _
    exact le_trans hpow.le I.scaleRadius.1
  let N : Finset (Fin k) := Finset.univ.filter fun a =>
    i ∈ cube d m (I.anchor a) (100 * I.Ds)
  let H : Finset (Fin k) := Finset.univ.filter fun a =>
    i ∈ cube d m (I.anchor a) (200 * I.Ds)
  have hsub : N ⊆ H := by
    intro a ha
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    exact cube_hundred_subset_twohundred d m (I.anchor a) I.Ds hDs ha
  have hcard : N.card ≤ H.card := Finset.card_le_card hsub
  have hcardR : (N.card : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hcard
  have hover : (H.card : ℝ) ≤ I.C * t ^ (-(d : ℝ) * nu d) := by
    simpa [H, overlap] using I.haloOverlap i
  exact hcardR.trans hover

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_near_operation_count
