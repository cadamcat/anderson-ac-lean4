import AndersonAC.S78MatrixBounds.Diagonal
import AndersonAC.S78MatrixBounds.Algebra
import AndersonAC.S78MatrixBounds.AnchorSums
import AndersonAC.S78.ExponentialTail
import AndersonAC.S78Scale.Proofs
import AndersonAC.S78AnchorTail.Proof

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Near operations are counted by halo overlap; far operations have a
uniform summable row-ℓ² envelope. -/
theorem assembly_rowL2_increment_sum_bound (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ A K t₀ : ℝ, 0 ≤ A ∧ 0 < K ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
        (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
        ∀ i : Torus d m,
          (∑ q : Fin k, rowL2Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j)) ≤
            A * t ^ (0.125 * delta - (d : ℝ) * nu d) + K * t := by
  let γ : ℝ := c / 4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨Pfar, tTail, hPfar, htTail, hTail⟩ :=
    AndersonAC.SolS78.assemblyAnchorTailInput_proof d hd C c P hC hc hP
  obtain ⟨Mcol, tCol, hMcol, htCol, hColumnMoment⟩ :=
    graph_exponential_moment d hd (2 * γ) (mul_pos (by norm_num) hγ)
  obtain ⟨Manchor, tAnchor, hManchor, htAnchor, hAnchorMoment⟩ :=
    injective_anchor_exponential_sum d hd γ hγ
  obtain ⟨tExp, htExp, hExp⟩ :=
    AndersonAC.SolS78.assembly_exponential_tail γ
      (Pfar + (3 / 2 : ℝ) * (d : ℝ)) 1 1 hγ (by norm_num)
  have hMcolSqrt : 0 < Real.sqrt Mcol := Real.sqrt_pos.2 hMcol
  let A : ℝ := C * Real.sqrt C
  let K : ℝ := Real.sqrt Mcol * Manchor
  let t₀ : ℝ := min tTail (min tCol (min tAnchor tExp))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; exact mul_pos hMcolSqrt hManchor
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact lt_min htTail (lt_min htCol (lt_min htAnchor htExp))
  refine ⟨A, K, t₀, hA, hK, ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall i
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have htTailSmall : t < tTail := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htOther : t < min tCol (min tAnchor tExp) :=
    lt_of_lt_of_le htSmall (min_le_right _ _)
  have htColSmall : t < tCol := lt_of_lt_of_le htOther (min_le_left _ _)
  have htLast : t < min tAnchor tExp := lt_of_lt_of_le htOther (min_le_right _ _)
  have htAnchorSmall : t < tAnchor := lt_of_lt_of_le htLast (min_le_left _ _)
  have htExpSmall : t < tExp := lt_of_lt_of_le htLast (min_le_right _ _)
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
      t ^ (-(Pfar + (3 / 2 : ℝ) * (d : ℝ))) * Real.exp (-γ * t * I.Ds) ≤ t := by
    have h := hExp t I.Ds ht htExpSmall hDsTail
    simpa [Real.rpow_one] using h
  let near : Finset (Fin k) := Finset.univ.filter fun q =>
    i ∈ cube d m (I.anchor q) (100 * I.Ds)
  let far : Finset (Fin k) := Finset.univ.filter fun q =>
    i ∉ cube d m (I.anchor q) (100 * I.Ds)
  have hnearCount : (near.card : ℝ) ≤ C * t ^ (-(d : ℝ) * nu d) := by
    simpa [near, hIC] using assembly_near_operation_count I i
  have hpowNear :
      t ^ (-(d : ℝ) * nu d) * t ^ (0.125 * delta) =
        t ^ (0.125 * delta - (d : ℝ) * nu d) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hrootPower : Real.sqrt (t ^ (0.25 * delta)) = t ^ (0.125 * delta) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hnearPoint (q : Fin k) :
      rowL2Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j) ≤
        Real.sqrt C * t ^ (0.125 * delta) := by
    let Δ : Matrix (Torus d m) (Torus d m) ℂ :=
      survivorDifference (I.state q.castSucc) (I.state q.succ) t
    have hrow : rowTwo Δ i ≤ C * t ^ (0.25 * delta) := by
      simpa [Δ, hIC] using I.rowChange q i
    have hrootEq : Real.sqrt (rowTwo Δ i) = rowL2Root (fun j => Δ i j) := by
      rw [rowTwo_eq_rowL2Root_sq]
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg (rowL2Root_nonneg _)
    have hroot := Real.sqrt_le_sqrt hrow
    rw [hrootEq] at hroot
    rw [Real.sqrt_mul (by positivity), hrootPower] at hroot
    simpa [Δ] using hroot
  have hFarPoint (q : Fin k) (hq : q ∈ far) :
      rowL2Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j) ≤
        Real.sqrt Mcol * t ^ (-(Pfar + (d : ℝ) / 2)) *
          Real.exp (-γ * t * I.Ds) *
          Real.exp (-γ * t * physicalDistance d m i (I.anchor q)) := by
    let Δ : Matrix (Torus d m) (Torus d m) ℂ :=
      survivorDifference (I.state q.castSucc) (I.state q.succ) t
    let ρi : ℝ := physicalDistance d m i (I.anchor q)
    let B : ℝ := t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) * Real.exp (-γ * t * ρi)
    have hnot : i ∉ cube d m (I.anchor q) (100 * I.Ds) := by
      simpa [far] using hq
    have hρi : 0 ≤ ρi := by dsimp [ρi, physicalDistance]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hentry (j : Torus d m) :
        ‖Δ i j‖ ≤ B * Real.exp (-γ * t * physicalDistance d m j (I.anchor q)) := by
      have hraw := hTail m k t b r I hIC hIc hIP htTailSmall q i j (Or.inl hnot)
      have heq : t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
          Real.exp (-γ * t * (ρi + physicalDistance d m j (I.anchor q))) =
          B * Real.exp (-γ * t * physicalDistance d m j (I.anchor q)) := by
        have hexp : Real.exp (-γ * t * (ρi + physicalDistance d m j (I.anchor q))) =
            Real.exp (-γ * t * ρi) *
              Real.exp (-γ * t * physicalDistance d m j (I.anchor q)) := by
          calc
            _ = Real.exp ((-γ * t * ρi) +
                (-γ * t * physicalDistance d m j (I.anchor q))) := by
                  congr 1
                  ring
            _ = _ := Real.exp_add _ _
        dsimp [B]
        rw [hexp]
        ring
      exact hraw.trans_eq heq
    have hcolMoment := hColumnMoment m hside (I.anchor q) t ht htColSmall
    have hdistSymm (x : Torus d m) : physicalDistance d m (I.anchor q) x =
        physicalDistance d m x (I.anchor q) := by
      unfold physicalDistance
      exact congrArg (fun n : ℕ => (n : ℝ)) (nnGraph d m).dist_comm
    have hrowSq : rowTwo Δ i ≤ B ^ 2 *
        (∑ j, Real.exp (-(2 * γ) * t * physicalDistance d m j (I.anchor q))) := by
      unfold rowTwo
      calc
        (∑ j, ‖Δ i j‖ ^ 2) ≤
            ∑ j, (B * Real.exp
              (-γ * t * physicalDistance d m j (I.anchor q))) ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              exact sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (Real.exp_nonneg _)) |>.2 (hentry j)
        _ = B ^ 2 * (∑ j, Real.exp (-(2 * γ) * t * physicalDistance d m j (I.anchor q))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [mul_pow]
              congr 1
              rw [pow_two, ← Real.exp_add]
              congr 1
              ring
    have hMomentForm :
        (∑ j, Real.exp (-(2 * γ) * t * physicalDistance d m j (I.anchor q))) ≤
          Mcol * t ^ (-(d : ℝ)) := by
      calc
        _ = ∑ j, Real.exp (-(2 * γ) * t * physicalDistance d m (I.anchor q) j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hdistSymm]
        _ ≤ Mcol * t ^ (-(d : ℝ)) := by simpa using hcolMoment
    have hrowSq' : rowTwo Δ i ≤ B ^ 2 * (Mcol * t ^ (-(d : ℝ))) :=
      hrowSq.trans (mul_le_mul_of_nonneg_left hMomentForm (sq_nonneg B))
    have hrootEq : Real.sqrt (rowTwo Δ i) = rowL2Root (fun j => Δ i j) := by
      rw [rowTwo_eq_rowL2Root_sq]
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg (rowL2Root_nonneg _)
    have hsqrtPow : Real.sqrt (t ^ (-(d : ℝ))) = t ^ (-(d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      congr 1
      ring
    have hrootBound : rowL2Root (fun j => Δ i j) ≤
        B * (Real.sqrt Mcol * t ^ (-(d : ℝ) / 2)) := by
      rw [← hrootEq]
      calc
        Real.sqrt (rowTwo Δ i) ≤ Real.sqrt (B ^ 2 * (Mcol * t ^ (-(d : ℝ)))) :=
          Real.sqrt_le_sqrt hrowSq'
        _ = B * (Real.sqrt Mcol * t ^ (-(d : ℝ) / 2)) := by
          rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hB, Real.sqrt_mul hMcol.le]
          rw [hsqrtPow]
    have hpow : t ^ (-Pfar) * t ^ (-(d : ℝ) / 2) =
        t ^ (-(Pfar + (d : ℝ) / 2)) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hrootClean : rowL2Root (fun j => Δ i j) ≤
        Real.sqrt Mcol * t ^ (-(Pfar + (d : ℝ) / 2)) *
          Real.exp (-γ * t * I.Ds) * Real.exp (-γ * t * ρi) := by
      dsimp [B] at hrootBound
      calc
        rowL2Root (fun j => Δ i j) ≤
            t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) * Real.exp (-γ * t * ρi) *
              (Real.sqrt Mcol * t ^ (-(d : ℝ) / 2)) := hrootBound
        _ = Real.sqrt Mcol *
              (t ^ (-Pfar) * t ^ (-(d : ℝ) / 2)) *
              Real.exp (-γ * t * I.Ds) * Real.exp (-γ * t * ρi) := by ring
        _ = _ := by rw [hpow]
    simpa [Δ, ρi] using hrootClean
  have hfarSum :
      (∑ q ∈ far, rowL2Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j)) ≤ K * t := by
    have hsumAnchor := hAnchorMoment m k hside I.anchor I.distinct i t ht htAnchorSmall far
    have hFactor : 0 ≤ Real.sqrt Mcol *
        t ^ (-(Pfar + (d : ℝ) / 2)) * Real.exp (-γ * t * I.Ds) := by positivity
    have hpow : t ^ (-(Pfar + (d : ℝ) / 2)) * t ^ (-(d : ℝ)) =
        t ^ (-(Pfar + (3 / 2 : ℝ) * (d : ℝ))) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc
      _ ≤ ∑ q ∈ far, Real.sqrt Mcol * t ^ (-(Pfar + (d : ℝ) / 2)) *
          Real.exp (-γ * t * I.Ds) *
          Real.exp (-γ * t * physicalDistance d m i (I.anchor q)) :=
            Finset.sum_le_sum fun q hq => hFarPoint q hq
      _ = Real.sqrt Mcol * t ^ (-(Pfar + (d : ℝ) / 2)) *
          Real.exp (-γ * t * I.Ds) *
          (∑ q ∈ far, Real.exp (-γ * t * physicalDistance d m i (I.anchor q))) := by
            rw [← Finset.mul_sum]
      _ ≤ Real.sqrt Mcol * t ^ (-(Pfar + (d : ℝ) / 2)) *
          Real.exp (-γ * t * I.Ds) * (Manchor * t ^ (-(d : ℝ))) :=
            mul_le_mul_of_nonneg_left hsumAnchor hFactor
      _ = K * (t ^ (-(Pfar + (3 / 2 : ℝ) * (d : ℝ))) *
          Real.exp (-γ * t * I.Ds)) := by
            dsimp [K]
            calc
              _ = (Real.sqrt Mcol * Manchor) *
                    (t ^ (-(Pfar + (d : ℝ) / 2)) * t ^ (-(d : ℝ))) *
                    Real.exp (-γ * t * I.Ds) := by ring
              _ = (Real.sqrt Mcol * Manchor) *
                    t ^ (-(Pfar + (3 / 2 : ℝ) * (d : ℝ))) *
                    Real.exp (-γ * t * I.Ds) := by rw [hpow]
              _ = _ := by ring
      _ ≤ K * t := mul_le_mul_of_nonneg_left hFarEnvelope (le_of_lt hK)
  have hnearSum :
      (∑ q ∈ near, rowL2Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j)) ≤
        A * t ^ (0.125 * delta - (d : ℝ) * nu d) := by
    have hpointNonneg (q : Fin k) :
        0 ≤ rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j) := rowL2Root_nonneg _
    calc
      _ ≤ ∑ q ∈ near, Real.sqrt C * t ^ (0.125 * delta) :=
          Finset.sum_le_sum fun q hq => hnearPoint q
      _ = (near.card : ℝ) * (Real.sqrt C * t ^ (0.125 * delta)) := by simp
      _ ≤ (C * t ^ (-(d : ℝ) * nu d)) *
          (Real.sqrt C * t ^ (0.125 * delta)) :=
            mul_le_mul_of_nonneg_right hnearCount (by positivity)
      _ = A * t ^ (0.125 * delta - (d : ℝ) * nu d) := by
            dsimp [A]
            calc
              _ = (C * Real.sqrt C) *
                    (t ^ (-(d : ℝ) * nu d) * t ^ (0.125 * delta)) := by ring
              _ = _ := by rw [hpowNear]
  have hsplit :
      (∑ q : Fin k, rowL2Root (fun j => survivorDifference
        (I.state q.castSucc) (I.state q.succ) t i j)) =
        (∑ q ∈ near, rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) +
        (∑ q ∈ far, rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) := by
    simpa [near, far] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin k)))
        (p := fun q : Fin k => i ∈ cube d m (I.anchor q) (100 * I.Ds))
        (f := fun q : Fin k => rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j))).symm
  calc
    _ = (∑ q ∈ near, rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) +
        (∑ q ∈ far, rowL2Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) := hsplit
    _ ≤ A * t ^ (0.125 * delta - (d : ℝ) * nu d) + K * t :=
      add_le_add hnearSum hfarSum

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_rowL2_increment_sum_bound
