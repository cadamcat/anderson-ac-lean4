import AndersonAC.S78MatrixBounds.Near
import AndersonAC.S78MatrixBounds.Telescoping
import AndersonAC.S78MatrixBounds.AnchorSums
import AndersonAC.S78.ExponentialTail
import AndersonAC.S78Scale.Proofs
import AndersonAC.S78AnchorTail.Proof

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Telescoping the active diagonal gives the scale-sharp lag estimate. -/
theorem assembly_diagonal_bound (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
        (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
        ∀ (a : Fin (k + 1)) (i : Torus d m), i ∈ (I.state a).active →
          ‖(I.state a).g i i - r i‖ ≤ C' * t ^ (0.42 * delta - (d : ℝ) * nu d) := by
  have hdnu : (d : ℝ) * nu d = 0.00001 * delta :=
    (assembly_exponent_margins_proof d hd).1
  let p : ℝ := 0.42 * delta - (d : ℝ) * nu d
  have hp : 0 < p := by
    dsimp [p]
    rw [hdnu]
    norm_num [delta]
  have hpHalf : p ≤ (1 / 2 : ℝ) := by
    dsimp [p]
    rw [hdnu]
    norm_num [delta]
  let γ : ℝ := c / 4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨Pfar, tTail, hPfar, htTail, hAnchorTail⟩ :=
    AndersonAC.SolS78.assemblyAnchorTailInput_proof d hd C c P hC hc hP
  obtain ⟨Mexp, tMoment, hMexp, htMoment, hAnchorMoment⟩ :=
    injective_anchor_exponential_sum d hd γ hγ
  obtain ⟨tExp, htExp, hExp⟩ :=
    AndersonAC.SolS78.assembly_exponential_tail γ (Pfar + (d : ℝ)) 1 1 hγ
      (by norm_num)
  let t₀ : ℝ := min tTail (min tMoment tExp)
  let C' : ℝ := C + C ^ 2 + Mexp
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact lt_min htTail (lt_min htMoment htExp)
  have hC' : 0 < C' := by
    dsimp [C']
    positivity
  refine ⟨C', t₀, hC', ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall a i hi
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have htTailSmall : t < tTail := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htPair : t < min tMoment tExp := lt_of_lt_of_le htSmall (min_le_right _ _)
  have htMomentSmall : t < tMoment := lt_of_lt_of_le htPair (min_le_left _ _)
  have htExpSmall : t < tExp := lt_of_lt_of_le htPair (min_le_right _ _)
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hpowDs : t ^ (-2 : ℝ) ≤ t ^ (-8 - nu d) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hpowOne : 1 ≤ t ^ (-2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (0 : ℝ) ≥ -2)
    simpa using h
  have hDsOne : 1 ≤ I.Ds := hpowOne.trans (hpowDs.trans I.scaleRadius.1)
  have hsideReal : (4 : ℝ) ≤ (OAI.Anderson.sideLength m : ℝ) := by
    have h400 : (400 : ℝ) ≤ 400 * I.Ds := by nlinarith [hDsOne]
    linarith [I.embedded]
  have hside : 4 ≤ OAI.Anderson.sideLength m := by exact_mod_cast hsideReal
  have hDsBelow : t ^ (-2 : ℝ) ≤ I.Ds := hpowDs.trans I.scaleRadius.1
  have hDsTail : t ^ (-1 - 1 : ℝ) ≤ I.Ds := by
    simpa [show (-1 - 1 : ℝ) = -2 by norm_num] using hDsBelow
  have hFarEnvelope :
      t ^ (-(Pfar + (d : ℝ))) * Real.exp (-γ * t * I.Ds) ≤ t := by
    have h := hExp t I.Ds ht htExpSmall hDsTail
    simpa [γ, Real.rpow_one] using h
  let near : Finset (Fin k) := Finset.univ.filter fun q =>
    i ∈ cube d m (I.anchor q) (100 * I.Ds)
  let far : Finset (Fin k) := Finset.univ.filter fun q =>
    i ∉ cube d m (I.anchor q) (100 * I.Ds)
  let Δ : Fin k → ℂ := fun q =>
    survivorDifference (I.state q.castSucc) (I.state q.succ) t i i
  let prefixOps : Finset (Fin k) := Finset.univ.filter fun q => q.val < a.val
  have hnearCount : (near.card : ℝ) ≤ C * t ^ (-(d : ℝ) * nu d) := by
    simpa [near, hIC] using assembly_near_operation_count I i
  have hentry (q : Fin k) :
      ‖Δ q‖ ≤ C * Real.sqrt t * t ^ (0.42 * delta) := by
    simpa [Δ, hIC] using I.entryChange q i i
  have hNearSum :
      (∑ q ∈ near, ‖Δ q‖) ≤ C ^ 2 * Real.sqrt t * t ^ p := by
    have hentryNonneg : 0 ≤ C * Real.sqrt t * t ^ (0.42 * delta) := by positivity
    have hpowNear :
        t ^ (-(d : ℝ) * nu d) * t ^ (0.42 * delta) = t ^ p := by
      rw [← Real.rpow_add ht]
      congr 1
      dsimp [p]
      ring
    calc
      (∑ q ∈ near, ‖Δ q‖) ≤
          ∑ q ∈ near, C * Real.sqrt t * t ^ (0.42 * delta) :=
            Finset.sum_le_sum (fun q hq => hentry q)
      _ = (near.card : ℝ) * (C * Real.sqrt t * t ^ (0.42 * delta)) := by simp
      _ ≤ (C * t ^ (-(d : ℝ) * nu d)) *
            (C * Real.sqrt t * t ^ (0.42 * delta)) :=
              mul_le_mul_of_nonneg_right hnearCount hentryNonneg
      _ = C ^ 2 * Real.sqrt t * (t ^ (-(d : ℝ) * nu d) * t ^ (0.42 * delta)) := by ring
      _ = C ^ 2 * Real.sqrt t * t ^ p := congrArg
        (fun z : ℝ => C ^ 2 * Real.sqrt t * z) hpowNear
  have hFarPoint (q : Fin k) (hq : q ∈ far) :
      ‖Δ q‖ ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
        Real.exp (-γ * t * physicalDistance d m i (I.anchor q)) := by
    have hnot : i ∉ cube d m (I.anchor q) (100 * I.Ds) := by
      simpa [far] using hq
    have hraw := hAnchorTail m k t b r I hIC hIc hIP htTailSmall q i i (Or.inl hnot)
    have hρ : 0 ≤ physicalDistance d m i (I.anchor q) := by
      dsimp [physicalDistance]
      positivity
    have harg :
        -γ * t * (physicalDistance d m i (I.anchor q) +
          physicalDistance d m i (I.anchor q)) ≤
        -γ * t * physicalDistance d m i (I.anchor q) := by
      have hnonneg := mul_nonneg (mul_nonneg hγ.le ht.le) hρ
      nlinarith
    calc
      ‖Δ q‖ ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
          Real.exp (-γ * t * (physicalDistance d m i (I.anchor q) +
            physicalDistance d m i (I.anchor q))) := by simpa [Δ, γ] using hraw
      _ ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
          Real.exp (-γ * t * physicalDistance d m i (I.anchor q)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
  have hFarSum : (∑ q ∈ far, ‖Δ q‖) ≤ Mexp * t := by
    have hAnchor := hAnchorMoment m k hside I.anchor I.distinct i t ht htMomentSmall far
    have hFactor : 0 ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) := by positivity
    calc
      (∑ q ∈ far, ‖Δ q‖) ≤
          ∑ q ∈ far, t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
            Real.exp (-γ * t * physicalDistance d m i (I.anchor q)) :=
              Finset.sum_le_sum fun q hq => hFarPoint q hq
      _ = t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
            (∑ q ∈ far, Real.exp (-γ * t * physicalDistance d m i (I.anchor q))) := by
              rw [← Finset.mul_sum]
      _ ≤ t ^ (-Pfar) * Real.exp (-γ * t * I.Ds) *
            (Mexp * t ^ (-(d : ℝ))) := mul_le_mul_of_nonneg_left hAnchor hFactor
      _ = Mexp * (t ^ (-Pfar) * t ^ (-(d : ℝ))) *
            Real.exp (-γ * t * I.Ds) := by ring
      _ = Mexp * (t ^ (-(Pfar + (d : ℝ)))) *
            Real.exp (-γ * t * I.Ds) := by
              have hpow : t ^ (-Pfar) * t ^ (-(d : ℝ)) =
                  t ^ (-(Pfar + (d : ℝ))) := by
                rw [← Real.rpow_add ht]
                congr 1
                ring
              rw [hpow]
      _ = Mexp * (t ^ (-(Pfar + (d : ℝ))) * Real.exp (-γ * t * I.Ds)) := by ring
      _ ≤ Mexp * t := mul_le_mul_of_nonneg_left hFarEnvelope hMexp.le
  have hprefixLe :
      (∑ q ∈ prefixOps, ‖Δ q‖) ≤
        (∑ q ∈ near, ‖Δ q‖) + (∑ q ∈ far, ‖Δ q‖) := by
    have hAll :
        (∑ q : Fin k, ‖Δ q‖) =
          (∑ q ∈ near, ‖Δ q‖) + (∑ q ∈ far, ‖Δ q‖) := by
      simpa [near, far, Δ] using
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin k)))
          (p := fun q : Fin k => i ∈ cube d m (I.anchor q) (100 * I.Ds))
          (f := fun q : Fin k => ‖survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i i‖)).symm
    calc
      (∑ q ∈ prefixOps, ‖Δ q‖) ≤ ∑ q : Fin k, ‖Δ q‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro q hq hqnot
        exact norm_nonneg _
      _ = (∑ q ∈ near, ‖Δ q‖) + (∑ q ∈ far, ‖Δ q‖) := hAll
  have hsumPrefix :
      (∑ q ∈ prefixOps, ‖Δ q‖) ≤ C ^ 2 * Real.sqrt t * t ^ p + Mexp * t :=
    hprefixLe.trans (add_le_add hNearSum hFarSum)
  have hi0 := active_initial_of_active I a i hi
  have hlag : ‖(I.state 0).g i i - r i‖ ≤ C * t ^ (0.42 * delta) := by
    simpa [hIC] using I.initialLag i hi0
  have htel := normalizedInverse_telescopes_active I a i i hi hi
  have htelErr :
      (Real.sqrt t : ℂ) * ((I.state a).g i i - r i) =
        (Real.sqrt t : ℂ) * ((I.state 0).g i i - r i) +
          ∑ q ∈ prefixOps, Δ q := by
    have htel' :
        (Real.sqrt t : ℂ) * (I.state a).g i i =
          (Real.sqrt t : ℂ) * (I.state 0).g i i +
            ∑ q ∈ prefixOps, Δ q := by
      simpa [normalizedInverse, prefixOps, Δ] using htel
    calc
      (Real.sqrt t : ℂ) * ((I.state a).g i i - r i) =
          (Real.sqrt t : ℂ) * (I.state a).g i i - (Real.sqrt t : ℂ) * r i := by ring
      _ = ((Real.sqrt t : ℂ) * (I.state 0).g i i + ∑ q ∈ prefixOps, Δ q) -
          (Real.sqrt t : ℂ) * r i := by rw [htel']
      _ = (Real.sqrt t : ℂ) * ((I.state 0).g i i - r i) +
          ∑ q ∈ prefixOps, Δ q := by ring
  have hscale (z : ℂ) :
      ‖(Real.sqrt t : ℂ) * z‖ = Real.sqrt t * ‖z‖ := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsumPrefixAdded :
      Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
          ∑ q ∈ prefixOps, ‖Δ q‖ ≤
        Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
          (C ^ 2 * Real.sqrt t * t ^ p + Mexp * t) := by
    calc
      _ = (∑ q ∈ prefixOps, ‖Δ q‖) +
          Real.sqrt t * ‖(I.state 0).g i i - r i‖ := by ring
      _ ≤ (C ^ 2 * Real.sqrt t * t ^ p + Mexp * t) +
          Real.sqrt t * ‖(I.state 0).g i i - r i‖ :=
            add_le_add_left hsumPrefix _
      _ = _ := by ring
  have hnormPrefix :
      ‖∑ q ∈ prefixOps, Δ q‖ ≤ ∑ q ∈ prefixOps, ‖Δ q‖ := norm_sum_le _ _
  have hscaled :
      Real.sqrt t * ‖(I.state a).g i i - r i‖ ≤
        Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
          ∑ q ∈ prefixOps, ‖Δ q‖ := by
    calc
      Real.sqrt t * ‖(I.state a).g i i - r i‖ =
          ‖(Real.sqrt t : ℂ) * ((I.state a).g i i - r i)‖ := (hscale _).symm
      _ = ‖(Real.sqrt t : ℂ) * ((I.state 0).g i i - r i) +
            ∑ q ∈ prefixOps, Δ q‖ := by rw [htelErr]
      _ ≤ ‖(Real.sqrt t : ℂ) * ((I.state 0).g i i - r i)‖ +
            ‖∑ q ∈ prefixOps, Δ q‖ := norm_add_le _ _
      _ ≤ Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
            ∑ q ∈ prefixOps, ‖Δ q‖ := by rw [hscale]; exact add_le_add_right hnormPrefix _
  have hbasePow : t ^ (0.42 * delta) ≤ t ^ p := by
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    dsimp [p]
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity) hnu]
  have hrootPow : Real.sqrt t ≤ t ^ p := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    dsimp [p]
    rw [hdnu]
    norm_num [delta]
  have hfarPow : t ≤ Real.sqrt t * t ^ p := by
    calc
      t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
      _ = Real.sqrt t * Real.sqrt t := by ring
      _ ≤ Real.sqrt t * t ^ p := mul_le_mul_of_nonneg_left hrootPow (Real.sqrt_nonneg _)
  have hinitScaled :
      Real.sqrt t * (C * t ^ (0.42 * delta)) ≤ C * Real.sqrt t * t ^ p := by
    calc
      Real.sqrt t * (C * t ^ (0.42 * delta)) =
          (C * Real.sqrt t) * t ^ (0.42 * delta) := by ring
      _ ≤ (C * Real.sqrt t) * t ^ p :=
        mul_le_mul_of_nonneg_left hbasePow (mul_nonneg (by linarith [hC]) (Real.sqrt_nonneg _))
      _ = C * Real.sqrt t * t ^ p := by ring
  have hfarScaled : Mexp * t ≤ Mexp * Real.sqrt t * t ^ p := by
    calc
      Mexp * t ≤ Mexp * (Real.sqrt t * t ^ p) := mul_le_mul_of_nonneg_left hfarPow hMexp.le
      _ = Mexp * Real.sqrt t * t ^ p := by ring
  have hscaledBound :
      Real.sqrt t * ‖(I.state a).g i i - r i‖ ≤
        (C + C ^ 2 + Mexp) * Real.sqrt t * t ^ p := by
    calc
      _ ≤ Real.sqrt t * (C * t ^ (0.42 * delta)) +
            (C ^ 2 * Real.sqrt t * t ^ p + Mexp * t) := by
              calc
                _ ≤ Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
                    ∑ q ∈ prefixOps, ‖Δ q‖ := hscaled
                _ ≤ Real.sqrt t * ‖(I.state 0).g i i - r i‖ +
                    (C ^ 2 * Real.sqrt t * t ^ p + Mexp * t) :=
                      hsumPrefixAdded
                _ ≤ Real.sqrt t * (C * t ^ (0.42 * delta)) +
                    (C ^ 2 * Real.sqrt t * t ^ p + Mexp * t) :=
                      add_le_add (mul_le_mul_of_nonneg_left hlag (Real.sqrt_nonneg _)) le_rfl
      _ ≤ C * Real.sqrt t * t ^ p +
            (C ^ 2 * Real.sqrt t * t ^ p + Mexp * Real.sqrt t * t ^ p) :=
              add_le_add hinitScaled (add_le_add_right hfarScaled _)
      _ = (C + C ^ 2 + Mexp) * Real.sqrt t * t ^ p := by ring
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hfinal :
      ‖(I.state a).g i i - r i‖ ≤ (C + C ^ 2 + Mexp) * t ^ p := by
    have hscaledBound' :
        Real.sqrt t * ‖(I.state a).g i i - r i‖ ≤
          Real.sqrt t * ((C + C ^ 2 + Mexp) * t ^ p) := by
      calc
        _ ≤ (C + C ^ 2 + Mexp) * Real.sqrt t * t ^ p := hscaledBound
        _ = _ := by ring
    have := (mul_le_mul_iff_of_pos_left hsqrt).mp hscaledBound'
    exact this
  simpa [C', p] using hfinal

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_diagonal_bound
