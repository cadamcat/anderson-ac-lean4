import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78BridgeEnergy.Basic
import AndersonAC.S78BridgeEnergy.Weights
import AndersonAC.S78AnchorTail.Geometry
import AndersonAC.S78Moment.Geometry

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Sites outside a cube are far in graph distance. -/
theorem outside_cube_lower {d m : ℕ} (x z : Torus d m) (R : ℝ)
    (hx : x ∉ cube d m z R) : R < physicalDistance d m x z := by
  classical
  have hnot : ¬ ∀ q : Fin d,
      ((min ((x q - z q).val) (OAI.Anderson.sideLength m - (x q - z q).val) : ℕ) : ℝ) ≤ R := by
    simpa [cube] using hx
  push_neg at hnot
  obtain ⟨q, hq⟩ := hnot
  exact lt_of_lt_of_le hq
    (AndersonAC.SolS78AnchorTail.coordNat_le_physicalDistance q x z)

/-- Translation preserves adjacency, hence distance. -/
private theorem shift_adj' {d m : ℕ} (a x y : Torus d m)
    (h : (nnGraph d m).Adj x y) : (nnGraph d m).Adj (x + a) (y + a) := by
  rcases (AndersonAC.SolS78.nnGraph_adj_iff_proof x y).mp h with ⟨hne, i, h1 | h2 | h3 | h4⟩
  · apply (AndersonAC.SolS78.nnGraph_adj_iff_proof _ _).mpr
    refine ⟨?_, i, Or.inl ?_⟩
    · intro he
      exact hne (add_right_cancel he)
    · rw [h1]; abel
  · apply (AndersonAC.SolS78.nnGraph_adj_iff_proof _ _).mpr
    refine ⟨?_, i, Or.inr (Or.inl ?_)⟩
    · intro he
      exact hne (add_right_cancel he)
    · rw [h2]; abel
  · apply (AndersonAC.SolS78.nnGraph_adj_iff_proof _ _).mpr
    refine ⟨?_, i, Or.inr (Or.inr (Or.inl ?_))⟩
    · intro he
      exact hne (add_right_cancel he)
    · rw [h3]; abel
  · apply (AndersonAC.SolS78.nnGraph_adj_iff_proof _ _).mpr
    refine ⟨?_, i, Or.inr (Or.inr (Or.inr ?_))⟩
    · intro he
      exact hne (add_right_cancel he)
    · rw [h4]; abel

/-- One direction of translation invariance, via mapped walks. -/
private theorem dist_shift_le (d m : ℕ) (a x y : Torus d m) :
    (nnGraph d m).dist (x + a) (y + a) ≤ (nnGraph d m).dist x y := by
  obtain ⟨p, hp⟩ :=
    AndersonAC.SolS78.nnGraph_connected_proof.exists_walk_length_eq_dist x y
  let hom1 : (nnGraph d m) →g (nnGraph d m) :=
    ⟨fun z => z + a, fun h => shift_adj' a _ _ h⟩
  have hle : (nnGraph d m).dist (x + a) (y + a) ≤ (p.map hom1).length :=
    SimpleGraph.dist_le _
  have hlen : (p.map hom1).length = p.length :=
    SimpleGraph.Walk.length_map _ _
  omega

/-- Graph distance on the torus is translation invariant. -/
theorem dist_shift (d m : ℕ) (a x y : Torus d m) :
    physicalDistance d m (x + a) (y + a) = physicalDistance d m x y := by
  unfold physicalDistance
  apply le_antisymm
  · exact_mod_cast dist_shift_le d m a x y
  · have h := dist_shift_le d m (-a) (x + a) (y + a)
    have e1 : (x + a) + (-a) = x := by abel
    have e2 : (y + a) + (-a) = y := by abel
    rw [e1, e2] at h
    exact_mod_cast h

/-- The clearing radius dominates the Combes–Thomas margin for `t ≤ 1`. -/
theorem Ds_ge_mprime {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (ht : 0 < t) (ht1 : t ≤ 1) :
    t ^ (-1.03 : ℝ) ≤ I.Ds := by
  have h1 : t ^ (-1.03 : ℝ) ≤ t ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by
      have hν : 0 ≤ nu d := by unfold nu delta; positivity
      linarith)
  exact h1.trans I.scaleRadius.1

/-- Far bridge weights decay exponentially in the anchor distance. -/
theorem far_weight_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 < c)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (a : Fin k) (i : Torus d m)
    (hi : i ∉ cube d m (I.anchor a) (100 * I.Ds)) :
    ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 ≤
      (C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hD100 : 100 * I.Ds < physicalDistance d m i (I.anchor a) :=
    outside_cube_lower i (I.anchor a) _ hi
  have hDsm : t ^ (-1.03 : ℝ) ≤ I.Ds := Ds_ge_mprime I ht ht1
  have hDsnn : 0 ≤ I.Ds := le_trans (Real.rpow_nonneg ht.le _) I.scaleRadius.1
  have hDnn : 0 ≤ physicalDistance d m i (I.anchor a) := Nat.cast_nonneg _
  -- Per-site bound.
  have hsite : ∀ x ∈ removedSet I a,
      (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 ≤
        C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
          Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a))) := by
    intro x hx
    have hxmem : x ∈ (I.state a.castSucc).active \ (I.state a.succ).active := hx
    have hxz : physicalDistance d m x (I.anchor a) ≤ I.Ds :=
      I.removedLocal a x hxmem
    have htri := AndersonAC.SolS78AnchorTail.physicalDistance_triangle d m i x (I.anchor a)
    have hmax8 : physicalDistance d m i (I.anchor a) / 8 ≤
        max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0 := by
      have h8 : physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ) ≥
          physicalDistance d m i (I.anchor a) / 8 := by
        nlinarith [htri, hxz, hDsm, hD100, hDsnn, hDnn]
      exact h8.trans (le_max_left _ _)
    have hdecay := I.resolventDecay a.castSucc i x
    rw [hIC, hIc] at hdecay
    have hsq : ‖oldInv I a i x‖ ^ 2 ≤ (C ^ 2 * t ^ (-1 : ℝ)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by
      have e1 : ‖oldInv I a i x‖ ^ 2 ≤
          (C / Real.sqrt t * Real.exp (-c * t *
            max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdecay 2
      have e2 : (C / Real.sqrt t * Real.exp (-c * t *
          max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 =
          (C ^ 2 * t ^ (-1 : ℝ)) *
            (Real.exp (-c * t *
              max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 := by
        rw [mul_pow, div_pow, Real.sq_sqrt ht.le, div_eq_mul_inv, ← Real.rpow_neg_one]
      have e3 : (Real.exp (-c * t *
          max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 ≤
          Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by
        have hnonpos : -c * t *
            max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) ht.le)
            (le_max_right _ _)
        have hsq1 : (Real.exp (-c * t *
            max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 ≤
            Real.exp (-c * t *
              max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0) := by
          calc (Real.exp _) ^ 2 = Real.exp _ * Real.exp _ := by ring
            _ ≤ 1 * Real.exp _ :=
                mul_le_mul_of_nonneg_right
                  (Real.exp_le_one_iff.mpr hnonpos) (Real.exp_pos _).le
            _ = _ := one_mul _
        have hmono : Real.exp (-c * t *
            max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0) ≤
            Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by
          apply Real.exp_le_exp.mpr
          have hct : 0 ≤ c * t := mul_nonneg hc.le ht.le
          nlinarith [hmax8, hct, hDnn]
        exact hsq1.trans hmono
      calc ‖oldInv I a i x‖ ^ 2 ≤ _ := e1
        _ = (C ^ 2 * t ^ (-1 : ℝ)) *
            (Real.exp (-c * t *
              max (physicalDistance d m i x / 2 - t ^ (-1.03 : ℝ)) 0)) ^ 2 := e2
        _ ≤ (C ^ 2 * t ^ (-1 : ℝ)) *
            Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
    calc (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
        ≤ C ^ 2 * ‖oldInv I a i x‖ ^ 2 := by
          have hprod : (r i).im * (r x).im ≤ C ^ 2 := by
            simpa only [pow_two] using
              mul_le_mul (hdamp i).2 (hdamp x).2 (hdamp x).1 hC0
          exact mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
      _ ≤ C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
          Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a))) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
          Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a))) := rfl
  -- Sum over the removed set.
  have hcard := card_removed_le I C hC hIC ht a
  have hexp_nn : 0 ≤ Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) :=
    (Real.exp_pos _).le
  calc ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
      ≤ ∑ _x ∈ removedSet I a, C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a))) :=
        Finset.sum_le_sum fun x hx => hsite x hx
    _ = ((removedSet I a).card : ℝ) * (C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * t ^ (-1 - heatExponent)) * (C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by
        have hexp : t ^ (-1 - heatExponent) * t ^ (-1 : ℝ) = t ^ (-2 - heatExponent) := by
          rw [← Real.rpow_add ht]
          congr 1
          ring
        calc (C * t ^ (-1 - heatExponent)) * (C ^ 2 * ((C ^ 2 * t ^ (-1 : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a))))
            = (C * C ^ 2 * C ^ 2) * (t ^ (-1 - heatExponent) * t ^ (-1 : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by ring
          _ = (C ^ 5 * t ^ (-2 - heatExponent)) * Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := by rw [hexp]; ring

/-- Extract the uniform `Ds` decay from the far exponential, keeping rate `c/16`
for the spatial sums. Needs `100·Ds ≤ dist`. -/
theorem exp_extract {c t D Ds : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hD : 100 * Ds ≤ D) (hDs : 0 ≤ Ds) :
    Real.exp (-(c / 8) * t * D) ≤
      Real.exp (-(c / 8) * t * (50 * Ds)) * Real.exp (-(c / 16) * t * D) := by
  have hle : -(c / 8) * t * D ≤ (-(c / 8) * t * (50 * Ds)) + ((-(c / 16)) * t * D) := by
    have hct : 0 ≤ (c / 16) * t := by positivity
    have key : (-(c / 8) * t * (50 * Ds)) + ((-(c / 16)) * t * D) - (-(c / 8) * t * D)
        = ((c / 16) * t) * (D - 100 * Ds) := by ring
    have hnn : 0 ≤ ((c / 16) * t) * (D - 100 * Ds) :=
      mul_nonneg hct (by linarith)
    linarith [key, hnn]
  have h := Real.exp_le_exp.mpr hle
  rwa [Real.exp_add] at h

/-- `(a + b + c)^2 ≤ 3(a^2 + b^2 + c^2)`. -/
theorem add3_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

end AndersonAC.S78BridgeEnergy
