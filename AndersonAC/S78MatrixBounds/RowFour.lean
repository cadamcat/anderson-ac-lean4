import AndersonAC.S78MatrixBounds.Algebra
import AndersonAC.S78MatrixBounds.Telescoping
import AndersonAC.S78Row.Row
import AndersonAC.S78MatrixBounds.AnchorSums
import AndersonAC.S78.ExponentialTail
import AndersonAC.S78AnchorTail.Proof

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Restricting a retained row to the final active set preserves the exact
prefix telescope; ℓ⁴ Minkowski then sums the survivor increments. -/
theorem active_row_l4_prefix_bound {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r)
    (a : Fin (k + 1)) (i : Torus d m) (hi : i ∈ (I.state a).active) :
    rowL4Root (fun j => normalizedInverse (I.state a) t i j) ≤
      rowL4Root (fun j => normalizedInverse (I.state 0) t i j) +
        ∑ q ∈ Finset.univ.filter (fun q : Fin k => q.val < a.val),
          rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j) := by
  classical
  let A := (I.state a).active
  let prefixOps : Finset (Fin k) := Finset.univ.filter fun q => q.val < a.val
  let v₀ : Torus d m → ℂ := fun j =>
    if j ∈ A then normalizedInverse (I.state 0) t i j else 0
  let inc : Fin k → Torus d m → ℂ := fun q j =>
    if j ∈ A then survivorDifference (I.state q.castSucc) (I.state q.succ) t i j else 0
  let finalRow : Torus d m → ℂ := fun j => normalizedInverse (I.state a) t i j
  have hrow (j : Torus d m) :
      finalRow j = v₀ j + ∑ q ∈ prefixOps, inc q j := by
    by_cases hj : j ∈ A
    · have htel := normalizedInverse_telescopes_active I a i j hi hj
      simpa [finalRow, v₀, inc, prefixOps, A, hj] using htel
    · have hsupport := (I.physical a).2.1 i j (Or.inr hj)
      have hzero : normalizedInverse (I.state a) t i j = 0 := by
        simp [normalizedInverse, hsupport]
      simp [finalRow, v₀, inc, A, hj, hzero]
  have hdecomp :
      finalRow = v₀ + fun j => ∑ q ∈ prefixOps, inc q j := by
    funext j
    exact hrow j
  calc
    rowL4Root (fun j => normalizedInverse (I.state a) t i j) =
        rowL4Root (v₀ + fun j => ∑ q ∈ prefixOps, inc q j) := by
          rw [← hdecomp]
    _ ≤ rowL4Root v₀ + rowL4Root (fun j => ∑ q ∈ prefixOps, inc q j) :=
          rowL4Root_add_le _ _
    _ ≤ rowL4Root v₀ + ∑ q ∈ prefixOps, rowL4Root (inc q) :=
          add_le_add le_rfl (rowL4Root_sum_le prefixOps inc)
    _ ≤ rowL4Root (fun j => normalizedInverse (I.state 0) t i j) +
          ∑ q ∈ prefixOps, rowL4Root (fun j =>
            survivorDifference (I.state q.castSucc) (I.state q.succ) t i j) := by
          apply add_le_add
          · exact rowL4Root_mask_le A (fun j => normalizedInverse (I.state 0) t i j)
          · apply Finset.sum_le_sum
            intro q hq
            exact rowL4Root_mask_le A (fun j =>
              survivorDifference (I.state q.castSucc) (I.state q.succ) t i j)

/-- The entry-change and row-change contracts imply the per-operation fourth
row bound needed by the finite ℓ⁴ telescope. -/
theorem survivor_increment_l4_bound {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) (q : Fin k)
    (i : Torus d m) :
    rowL4Root (fun j => survivorDifference (I.state q.castSucc)
      (I.state q.succ) t i j) ≤ I.C ^ 4 * t ^ ((1 + 1.09 * delta) / 4) := by
  rcases I.positive with ⟨ht, ht1, hb, hbt, hc, hCI, hP⟩
  let Δ : Matrix (Torus d m) (Torus d m) ℂ :=
    survivorDifference (I.state q.castSucc) (I.state q.succ) t
  let U : ℝ := I.C * Real.sqrt t * t ^ (0.42 * delta)
  let V : ℝ := I.C * t ^ (0.25 * delta)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hentry (j : Torus d m) : ‖Δ i j‖ ≤ U := by
    simpa [Δ, U] using I.entryChange q i j
  have hrow : rowTwo Δ i ≤ V := by
    simpa [Δ, V] using I.rowChange q i
  have hfour : rowFour Δ i ≤ U ^ 2 * V :=
    fourth_row_from_entry_and_two_proof Δ i U V hU hentry hrow
  have hpowProducts :
      (t ^ (0.42 * delta)) ^ 2 * t ^ (0.25 * delta) = t ^ (1.09 * delta) := by
    calc
      (t ^ (0.42 * delta)) ^ 2 * t ^ (0.25 * delta) =
          (t ^ (0.42 * delta) * t ^ (0.42 * delta)) * t ^ (0.25 * delta) := by
            rw [pow_two]
      _ = t ^ ((0.42 * delta) + (0.42 * delta) + (0.25 * delta)) := by
            rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      _ = t ^ (1.09 * delta) := by congr 1 <;> ring
  have hfourNumeric : rowFour Δ i ≤ I.C ^ 3 * t ^ (1 + 1.09 * delta) := by
    calc
      rowFour Δ i ≤ U ^ 2 * V := hfour
      _ = I.C ^ 3 * Real.sqrt t ^ 2 *
            ((t ^ (0.42 * delta)) ^ 2 * t ^ (0.25 * delta)) := by
              dsimp [U, V]
              ring
      _ = I.C ^ 3 * t * t ^ (1.09 * delta) := by
            rw [Real.sq_sqrt ht.le, hpowProducts]
      _ = I.C ^ 3 * t ^ (1 + 1.09 * delta) := by
            conv_rhs => rw [Real.rpow_add ht]
            simp [Real.rpow_one]
            ring
  let e : ℝ := (1 + 1.09 * delta) / 4
  have he : e * 4 = 1 + 1.09 * delta := by dsimp [e]; ring
  have htFourth : (t ^ e) ^ 4 = t ^ (1 + 1.09 * delta) := by
    calc
      (t ^ e) ^ 4 = (t ^ e) ^ (4 : ℝ) := (Real.rpow_natCast (t ^ e) 4).symm
      _ = t ^ (e * 4) := by rw [Real.rpow_mul ht.le]
      _ = t ^ (1 + 1.09 * delta) := by rw [he]
  have hpowTarget : (I.C ^ 4 * t ^ e) ^ 4 =
      I.C ^ 16 * t ^ (1 + 1.09 * delta) := by
    rw [mul_pow, show (I.C ^ 4) ^ 4 = I.C ^ 16 by ring, htFourth]
  have hCPow : I.C ^ 3 ≤ I.C ^ 16 := pow_le_pow_right₀ hCI (by omega)
  have hfourBound : rowFour Δ i ≤ (I.C ^ 4 * t ^ e) ^ 4 := by
    calc
      rowFour Δ i ≤ I.C ^ 3 * t ^ (1 + 1.09 * delta) := hfourNumeric
      _ ≤ I.C ^ 16 * t ^ (1 + 1.09 * delta) :=
        mul_le_mul_of_nonneg_right hCPow (Real.rpow_nonneg ht.le _)
      _ = (I.C ^ 4 * t ^ e) ^ 4 := hpowTarget.symm
  have hfourNonneg : 0 ≤ rowFour Δ i := by
    unfold rowFour
    positivity
  have hroot := Real.rpow_le_rpow hfourNonneg hfourBound (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hrootTarget : ((I.C ^ 4 * t ^ e) ^ 4) ^ (1 / 4 : ℝ) = I.C ^ 4 * t ^ e := by
    let B : ℝ := I.C ^ 4 * t ^ e
    calc
      (B ^ 4) ^ (1 / 4 : ℝ) = (B ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        exact congrArg (fun z : ℝ => z ^ (1 / 4 : ℝ)) (Real.rpow_natCast B 4).symm
      _ = B ^ ((4 : ℝ) * (1 / 4 : ℝ)) := by rw [Real.rpow_mul (by positivity)]
      _ = I.C ^ 4 * t ^ e := by norm_num [B, Real.rpow_one]
  rw [hrootTarget] at hroot
  simpa [rowL4Root, rowFour, Δ, e] using hroot

private theorem sqrt_anchor_tail_factor (t P γ D ρ : ℝ) (ht : 0 < t)
    (hγ : 0 < γ) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) :
    Real.sqrt (t ^ (-P) * Real.exp (-γ * t * D) * Real.exp (-γ * t * ρ)) =
      t ^ (-P / 2) * Real.exp (-(γ / 2) * t * D) * Real.exp (-(γ / 2) * t * ρ) := by
  have hpow : Real.sqrt (t ^ (-P)) = t ^ (-P / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (t ^ (-P)) ^ (1 / 2 : ℝ) = t ^ ((-P) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul ht.le (-P) (1 / 2 : ℝ)).symm
      _ = t ^ (-P / 2) := by congr 1 <;> ring
  have hexpD : Real.sqrt (Real.exp (-γ * t * D)) = Real.exp (-(γ / 2) * t * D) := by
    rw [← Real.exp_half]
    congr 1
    ring
  have hexpρ : Real.sqrt (Real.exp (-γ * t * ρ)) = Real.exp (-(γ / 2) * t * ρ) := by
    rw [← Real.exp_half]
    congr 1
    ring
  calc
    Real.sqrt (t ^ (-P) * Real.exp (-γ * t * D) * Real.exp (-γ * t * ρ)) =
        Real.sqrt (t ^ (-P)) * Real.sqrt (Real.exp (-γ * t * D)) *
          Real.sqrt (Real.exp (-γ * t * ρ)) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    _ = t ^ (-P / 2) * Real.exp (-(γ / 2) * t * D) *
          Real.exp (-(γ / 2) * t * ρ) := by rw [hpow, hexpD, hexpρ]

/-- Far fourth-row increments sum uniformly because their anchor envelope has
an exponential radius factor and the anchors are distinct. -/
theorem assembly_far_l4_root_sum_bound (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ K t₀ : ℝ, 0 < K ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
        (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
        ∀ (i : Torus d m) (F : Finset (Fin k)),
          (∀ q ∈ F, i ∉ cube d m (I.anchor q) (100 * I.Ds)) →
          (∑ q ∈ F, rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j)) ≤ K * t := by
  let γ : ℝ := c / 4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  let γh : ℝ := γ / 2
  have hγh : 0 < γh := by dsimp [γh]; positivity
  obtain ⟨Pfar, tTail, hPfar, htTail, hTail⟩ :=
    AndersonAC.SolS78.assemblyAnchorTailInput_proof d hd C c P hC hc hP
  obtain ⟨Mhalf, tMoment, hMhalf, htMoment, hAnchorMoment⟩ :=
    injective_anchor_exponential_sum d hd γh hγh
  obtain ⟨tExp, htExp, hExp⟩ :=
    AndersonAC.SolS78.assembly_exponential_tail γh (Pfar / 2 + (d : ℝ)) 1 1 hγh
      (by norm_num)
  let K : ℝ := C * Mhalf
  let t₀ : ℝ := min tTail (min tMoment tExp)
  have hK : 0 < K := by dsimp [K]; exact mul_pos (by linarith [hC]) hMhalf
  have ht₀ : 0 < t₀ := by dsimp [t₀]; exact lt_min htTail (lt_min htMoment htExp)
  refine ⟨K, t₀, hK, ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall i F hfar
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have htPair : t < min tMoment tExp := lt_of_lt_of_le htSmall (min_le_right _ _)
  have htMomentSmall : t < tMoment := lt_of_lt_of_le htPair (min_le_left _ _)
  have htExpSmall : t < tExp := lt_of_lt_of_le htPair (min_le_right _ _)
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hpowDs : t ^ (-2 : ℝ) ≤ t ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hDsBelow : t ^ (-2 : ℝ) ≤ I.Ds := hpowDs.trans I.scaleRadius.1
  have hpowOne : 1 ≤ t ^ (-2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (0 : ℝ) ≥ -2)
    simpa using h
  have hDsOne : 1 ≤ I.Ds := hpowOne.trans hDsBelow
  have hDsNonneg : 0 ≤ I.Ds := le_trans (by norm_num) hDsOne
  have hsideReal : (4 : ℝ) ≤ (OAI.Anderson.sideLength m : ℝ) := by
    have h400 : (400 : ℝ) ≤ 400 * I.Ds := by nlinarith [hDsOne]
    linarith [I.embedded]
  have hside : 4 ≤ OAI.Anderson.sideLength m := by exact_mod_cast hsideReal
  have hDsTail : t ^ (-1 - 1 : ℝ) ≤ I.Ds := by
    simpa [show (-1 - 1 : ℝ) = -2 by norm_num] using hDsBelow
  have hFarEnvelope :
      t ^ (-(Pfar / 2 + (d : ℝ))) * Real.exp (-γh * t * I.Ds) ≤ t := by
    have h := hExp t I.Ds ht htExpSmall hDsTail
    simpa [γh, Real.rpow_one] using h
  have hV : 0 ≤ C * t ^ (0.25 * delta) := by positivity
  have htV : t ^ (0.25 * delta) ≤ 1 := by
    have hδ : 0 ≤ (0.25 : ℝ) * delta := by unfold delta; positivity
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hδ
    simpa using h
  have hVle : C * t ^ (0.25 * delta) ≤ C := by
    calc
      C * t ^ (0.25 * delta) ≤ C * 1 := mul_le_mul_of_nonneg_left htV (by linarith [hC])
      _ = C := by ring
  have hVroot : (C * t ^ (0.25 * delta)) ^ (1 / 4 : ℝ) ≤ C := by
    calc
      _ ≤ C ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hV hVle (by norm_num : 0 ≤ (1 / 4 : ℝ))
      _ ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC (by norm_num)
      _ = C := by rw [Real.rpow_one]
  have hpoint (q : Fin k) (hq : q ∈ F) :
      rowL4Root (fun j => survivorDifference (I.state q.castSucc)
        (I.state q.succ) t i j) ≤
        C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          Real.exp (-γh * t * physicalDistance d m i (I.anchor q)) := by
    let Δ : Matrix (Torus d m) (Torus d m) ℂ :=
      survivorDifference (I.state q.castSucc) (I.state q.succ) t
    let U : ℝ := t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
      Real.exp (-γ * t * physicalDistance d m i (I.anchor q))
    let V : ℝ := C * t ^ (0.25 * delta)
    have hρ : 0 ≤ physicalDistance d m i (I.anchor q) := by
      dsimp [physicalDistance]
      positivity
    have hentry (j : Torus d m) : ‖Δ i j‖ ≤ U := by
      have hraw := hTail m k t b r I hIC hIc hIP (lt_of_lt_of_le htSmall (min_le_left _ _))
        q i j (Or.inl (hfar q hq))
      have hρj : 0 ≤ physicalDistance d m j (I.anchor q) := by
        dsimp [physicalDistance]
        positivity
      have harg :
          -γ * t * (physicalDistance d m i (I.anchor q) + physicalDistance d m j (I.anchor q)) ≤
            -γ * t * physicalDistance d m i (I.anchor q) := by
        have hnonneg := mul_nonneg (mul_nonneg hγ.le ht.le) hρj
        nlinarith
      calc
        ‖Δ i j‖ ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
            Real.exp (-γ * t * (physicalDistance d m i (I.anchor q) +
              physicalDistance d m j (I.anchor q))) := by simpa [Δ, γ] using hraw
        _ ≤ U := by
          dsimp [U]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    have hrow : rowTwo Δ i ≤ V := by simpa [Δ, V, hIC] using I.rowChange q i
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hroot := rowL4Root_entry_row Δ i U V hU hV hentry hrow
    have hrootFactor : Real.sqrt U =
        t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          Real.exp (-γh * t * physicalDistance d m i (I.anchor q)) := by
      simpa [U, γ, γh] using sqrt_anchor_tail_factor t Pfar γ I.Ds
        (physicalDistance d m i (I.anchor q)) ht hγ hDsNonneg hρ
    calc
      rowL4Root (fun j => survivorDifference (I.state q.castSucc)
          (I.state q.succ) t i j) ≤ Real.sqrt U * V ^ (1 / 4 : ℝ) := hroot
      _ ≤ Real.sqrt U * C := mul_le_mul_of_nonneg_left hVroot (Real.sqrt_nonneg _)
      _ = C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          Real.exp (-γh * t * physicalDistance d m i (I.anchor q)) := by
            rw [hrootFactor]
            ring
  have hFactor : 0 ≤ C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) := by positivity
  have hsumAnchor := hAnchorMoment m k hside I.anchor I.distinct i t ht htMomentSmall F
  have hsum :
      (∑ q ∈ F, rowL4Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j)) ≤ K * t := by
    calc
      _ ≤ ∑ q ∈ F, C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          Real.exp (-γh * t * physicalDistance d m i (I.anchor q)) :=
            Finset.sum_le_sum fun q hq => hpoint q hq
      _ = C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          (∑ q ∈ F, Real.exp (-γh * t * physicalDistance d m i (I.anchor q))) := by
            rw [← Finset.mul_sum]
      _ ≤ C * t ^ (-Pfar / 2) * Real.exp (-γh * t * I.Ds) *
          (Mhalf * t ^ (-(d : ℝ))) := mul_le_mul_of_nonneg_left hsumAnchor hFactor
      _ = C * Mhalf * (t ^ (-Pfar / 2) * t ^ (-(d : ℝ))) *
          Real.exp (-γh * t * I.Ds) := by ring
      _ = C * Mhalf * t ^ (-(Pfar / 2 + (d : ℝ))) *
          Real.exp (-γh * t * I.Ds) := by
            have hpow : t ^ (-Pfar / 2) * t ^ (-(d : ℝ)) =
                t ^ (-(Pfar / 2 + (d : ℝ))) := by
              rw [← Real.rpow_add ht]
              congr 1
              ring
            rw [hpow]
      _ = C * Mhalf *
          (t ^ (-(Pfar / 2 + (d : ℝ))) * Real.exp (-γh * t * I.Ds)) := by ring
      _ ≤ C * Mhalf * t :=
        mul_le_mul_of_nonneg_left hFarEnvelope
          (mul_nonneg (by linarith [hC]) hMhalf.le)
      _ = K * t := by rfl
  exact hsum
  
end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.active_row_l4_prefix_bound
#print axioms AndersonAC.SolS78.survivor_increment_l4_bound
#print axioms AndersonAC.SolS78.assembly_far_l4_root_sum_bound
