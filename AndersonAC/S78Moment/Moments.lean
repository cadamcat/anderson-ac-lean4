import AndersonAC.S78.Definitions
import AndersonAC.S78Moment.Geometry

open scoped BigOperators

namespace AndersonAC.SolS78

open AndersonAC.S78

private theorem physicalDistance_nonneg (d m : ℕ) (x y : Torus d m) :
    0 ≤ physicalDistance d m x y := by
  unfold physicalDistance
  exact_mod_cast Nat.zero_le ((nnGraph d m).dist x y)

private theorem shiftedPolynomialExponentialSummable (p : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (-c * (n : ℝ)) := by
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ p * Real.exp (-c * (n : ℝ)) :=
    Real.summable_pow_mul_exp_neg_nat_mul p hc
  have hsucc : Summable fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (-c * (n + 1 : ℝ)) := by
    have hsucc' := hbase.comp_injective Nat.succ_injective
    change Summable (fun n : ℕ => (Nat.succ n : ℝ) ^ p *
      Real.exp (-c * (Nat.succ n : ℝ))) at hsucc'
    simpa only [Nat.cast_succ] using hsucc'
  have hmul := hsucc.mul_left (Real.exp c)
  have heq : (fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (-c * (n : ℝ))) =
      fun n : ℕ => Real.exp c * ((n + 1 : ℝ) ^ p * Real.exp (-c * (n + 1 : ℝ))) := by
    funext n
    rw [show -c * (n : ℝ) = c + -c * ((n : ℝ) + 1) by ring, Real.exp_add]
    ring
  rw [heq]
  exact hmul

private theorem rpow_neg_nat_sum (t : ℝ) (ht : 0 < t) (d q : ℕ) :
    t ^ (-(d : ℝ) - (q : ℝ)) = (t⁻¹) ^ (d + q) := by
  have he : -(d : ℝ) - (q : ℝ) = -((d + q : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_neg (le_of_lt ht), Real.rpow_natCast, ← inv_pow]

set_option maxHeartbeats 500000 in
theorem lattice_exponential_moments_proof (d q : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m t, 0 < t → t ≤ 1 → ∀ x : Torus d m,
      (∑ y, Real.exp (-c * t * physicalDistance d m x y) * physicalDistance d m x y ^ q) ≤
        C * t ^ (-(d : ℝ) - (q : ℝ)) := by
  classical
  let p : ℕ := d + q
  let s : ℕ → ℝ := fun k => (k + 1 : ℝ) ^ p * Real.exp (-c * (k : ℝ))
  have hs : Summable s := by
    simpa [s, p] using shiftedPolynomialExponentialSummable (d + q) c hc
  let S : ℝ := ∑' k, s k
  let C : ℝ := (3 : ℝ) ^ d * (1 + S)
  have hS : 0 ≤ S := tsum_nonneg fun k => by positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro m t ht ht1 x
  let bin : Torus d m → ℕ := fun y => ⌊t * physicalDistance d m x y⌋₊
  let bins : Finset ℕ := Finset.univ.image bin
  let term : Torus d m → ℝ := fun y =>
    Real.exp (-c * t * physicalDistance d m x y) * physicalDistance d m x y ^ q
  have hpartition : (∑ y, term y) =
      ∑ k ∈ bins, ∑ y ∈ Finset.univ with bin y = k, term y := by
    have hsplit := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := bins) (g := bin)
      (fun y hy => Finset.mem_image_of_mem bin hy) term
    simpa [bins] using hsplit.symm
  have hbin (k : ℕ) :
      (∑ y ∈ Finset.univ with bin y = k, term y) ≤
        (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * s k := by
    let fiber : Finset (Torus d m) := Finset.univ.filter fun y => bin y = k
    let radius : ℕ := ⌊((k + 1 : ℝ) / t)⌋₊
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hRnonneg : 0 ≤ (k + 1 : ℝ) / t := by positivity
    have hRge : 1 ≤ (k + 1 : ℝ) / t := by
      rw [le_div_iff₀ ht]
      nlinarith [ht1]
    have hrad : (radius : ℝ) ≤ (k + 1 : ℝ) / t := Nat.floor_le hRnonneg
    have hfac : 2 * (radius : ℝ) + 1 ≤ 3 * ((k + 1 : ℝ) / t) := by
      nlinarith
    have hcard : fiber.card ≤ (2 * radius + 1) ^ d := by
      have hsub : fiber ⊆ Finset.univ.filter fun y : Torus d m =>
          (nnGraph d m).dist x y ≤ radius := by
        intro y hy
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hupper : t * physicalDistance d m x y < (k + 1 : ℝ) := by
          have hfloor := Nat.lt_succ_floor (t * physicalDistance d m x y)
          simpa [bin, hy] using hfloor
        have hdist : physicalDistance d m x y < (k + 1 : ℝ) / t := by
          rw [lt_div_iff₀ ht]
          nlinarith [hupper]
        have hdist' : ((nnGraph d m).dist x y : ℝ) ≤ (k + 1 : ℝ) / t := by
          simpa [physicalDistance] using hdist.le
        exact Nat.le_floor hdist'
      calc
        fiber.card ≤ (Finset.univ.filter fun y : Torus d m =>
            (nnGraph d m).dist x y ≤ radius).card := Finset.card_le_card hsub
        _ ≤ (2 * radius + 1) ^ d := graphBall_card_le x radius
    have hcardR : (fiber.card : ℝ) ≤ (3 * ((k + 1 : ℝ) / t)) ^ d := by
      calc
        (fiber.card : ℝ) ≤ ((2 * radius + 1) ^ d : ℕ) := by exact_mod_cast hcard
        _ = (2 * (radius : ℝ) + 1) ^ d := by norm_cast
        _ ≤ (3 * ((k + 1 : ℝ) / t)) ^ d := by
          exact pow_le_pow_left₀ (by positivity) hfac d
    have hpoint (y : Torus d m) (hy : y ∈ fiber) : term y ≤
        Real.exp (-c * (k : ℝ)) * (((k + 1 : ℝ) / t) ^ q) := by
      have hbinEq : bin y = k := by simpa [fiber] using hy
      have hkfloor : (k : ℝ) ≤ t * physicalDistance d m x y := by
        have hfloor := Nat.floor_le (mul_nonneg ht.le (physicalDistance_nonneg d m x y))
        simpa [bin, hbinEq] using hfloor
      have hupper : t * physicalDistance d m x y < (k + 1 : ℝ) := by
        have hfloor := Nat.lt_succ_floor (t * physicalDistance d m x y)
        simpa [bin, hbinEq] using hfloor
      have hdist : physicalDistance d m x y < (k + 1 : ℝ) / t := by
        rw [lt_div_iff₀ ht]
        nlinarith [hupper]
      have hexp : Real.exp (-c * t * physicalDistance d m x y) ≤
          Real.exp (-c * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hkfloor, hc]
      have hpow : physicalDistance d m x y ^ q ≤ ((k + 1 : ℝ) / t) ^ q := by
        exact pow_le_pow_left₀ (physicalDistance_nonneg d m x y) hdist.le q
      dsimp [term]
      exact mul_le_mul hexp hpow
        (pow_nonneg (physicalDistance_nonneg d m x y) q) (Real.exp_pos _).le
    have hsum : (∑ y ∈ fiber, term y) ≤
        (fiber.card : ℝ) * (Real.exp (-c * (k : ℝ)) * (((k + 1 : ℝ) / t) ^ q)) := by
      calc
        _ ≤ ∑ y ∈ fiber,
            Real.exp (-c * (k : ℝ)) * (((k + 1 : ℝ) / t) ^ q) :=
              Finset.sum_le_sum fun y hy => hpoint y hy
        _ = _ := by simp
    have hsum' : (∑ y ∈ fiber, term y) ≤
        (3 : ℝ) ^ d * ((t⁻¹) ^ (d + q)) *
          ((k + 1 : ℝ) ^ (d + q) * Real.exp (-c * (k : ℝ))) := by
      calc
        _ ≤ (fiber.card : ℝ) *
              (Real.exp (-c * (k : ℝ)) * (((k + 1 : ℝ) / t) ^ q)) := hsum
        _ ≤ (3 * ((k + 1 : ℝ) / t)) ^ d *
              (Real.exp (-c * (k : ℝ)) * (((k + 1 : ℝ) / t) ^ q)) :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = (3 : ℝ) ^ d * ((t⁻¹) ^ (d + q)) *
              ((k + 1 : ℝ) ^ (d + q) * Real.exp (-c * (k : ℝ))) := by
              calc
                _ = (3 : ℝ) ^ d * (((k + 1 : ℝ) * t⁻¹) ^ d) *
                    (((k + 1 : ℝ) * t⁻¹) ^ q) * Real.exp (-c * (k : ℝ)) := by
                      rw [div_eq_mul_inv, mul_pow]
                      ring
                _ = (3 : ℝ) ^ d *
                    ((((k + 1 : ℝ) * t⁻¹) ^ d) * (((k + 1 : ℝ) * t⁻¹) ^ q)) *
                    Real.exp (-c * (k : ℝ)) := by ring
                _ = (3 : ℝ) ^ d * (((k + 1 : ℝ) * t⁻¹) ^ (d + q)) *
                    Real.exp (-c * (k : ℝ)) := by rw [← pow_add]
                _ = (3 : ℝ) ^ d * (k + 1 : ℝ) ^ (d + q) *
                    (t⁻¹) ^ (d + q) * Real.exp (-c * (k : ℝ)) := by rw [mul_pow]; ring
                _ = _ := by ring
    simpa [s, p] using hsum'
  have hsumBins : (∑ k ∈ bins, ∑ y ∈ Finset.univ with bin y = k, term y) ≤
      (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * S := by
    calc
      _ ≤ ∑ k ∈ bins, (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * s k :=
        Finset.sum_le_sum fun k hk => hbin k
      _ = (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * ∑ k ∈ bins, s k := by
        rw [Finset.mul_sum]
      _ ≤ (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * S := by
        have hfinite : (∑ k ∈ bins, s k) ≤ ∑' k, s k :=
          Summable.sum_le_tsum bins (fun k hk => by positivity) hs
        dsimp [S]
        exact mul_le_mul_of_nonneg_left hfinite (by positivity)
  have hscale : t ^ (-(d : ℝ) - (q : ℝ)) = (t⁻¹) ^ (d + q) :=
    rpow_neg_nat_sum t ht d q
  calc
    (∑ y, term y) ≤ (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) * S := by
      rw [hpartition]
      exact hsumBins
    _ ≤ C * t ^ (-(d : ℝ) - (q : ℝ)) := by
      rw [hscale]
      dsimp [C]
      have hbase : 0 ≤ (3 : ℝ) ^ d * (t⁻¹) ^ (d + q) := by positivity
      nlinarith [hS]

end AndersonAC.SolS78
