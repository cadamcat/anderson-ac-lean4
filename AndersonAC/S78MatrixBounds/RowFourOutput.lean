import AndersonAC.S78MatrixBounds.RowFour
import AndersonAC.S78MatrixBounds.Near
import AndersonAC.S78Scale.Proofs

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The initial fourth-row margin and the near/far ℓ⁴ sums give the two
fourth-row outputs of the committed assembly contract. -/
theorem assembly_rowFour_output (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
        (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
        ∀ (a : Fin (k + 1)),
          (∀ i, rowL4Root (fun j => normalizedInverse (I.state a) t i j) ≤
            (0.7 ^ (1 / 4 : ℝ) + C' * t ^ (0.0225 * delta - (d : ℝ) * nu d)) *
              t ^ ((1 + delta) / 4)) ∧
          (∀ i, rowFour (normalizedInverse (I.state a) t) i < 0.8 * t ^ (1 + delta)) := by
  have hdnu : (d : ℝ) * nu d = 0.00001 * delta :=
    (assembly_exponent_margins_proof d hd).1
  have hcorr : 0 < 0.0225 * delta - (d : ℝ) * nu d :=
    (assembly_exponent_margins_proof d hd).2.2.1
  let α : ℝ := (1 + delta) / 4
  let ρ : ℝ := 0.0225 * delta - (d : ℝ) * nu d
  let β : ℝ := α + ρ
  let e : ℝ := (1 + 1.09 * delta) / 4
  have hbetaEq : e - (d : ℝ) * nu d = β := by
    dsimp [e, β, α, ρ]
    ring
  have hbetaLe : β ≤ 1 := by
    dsimp [β, α, ρ]
    rw [hdnu]
    norm_num [delta]
  obtain ⟨Kfar, tFar, hKfar, htFar, hFar⟩ :=
    assembly_far_l4_root_sum_bound d hd C c P hC hc hP
  let C' : ℝ := C ^ 5 + Kfar
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hgapBase : (0.7 : ℝ) ^ (1 / 4 : ℝ) < 0.8 ^ (1 / 4 : ℝ) := by
    apply Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  let gap : ℝ := 0.8 ^ (1 / 4 : ℝ) - 0.7 ^ (1 / 4 : ℝ)
  have hgap : 0 < gap := by dsimp [gap]; linarith [hgapBase]
  let η : ℝ := gap / (2 * C')
  have hη : 0 < η := by dsimp [η]; positivity
  let tStrict : ℝ := η ^ (1 / ρ)
  have htStrict : 0 < tStrict := by dsimp [tStrict]; positivity
  have hStrictPow : tStrict ^ ρ = η := by
    dsimp [tStrict]
    calc
      (η ^ (1 / ρ)) ^ ρ = η ^ ((1 / ρ) * ρ) :=
        (Real.rpow_mul hη.le (1 / ρ) ρ).symm
      _ = η := by
        have hmul : (1 / ρ) * ρ = 1 := by
          rw [one_div]
          exact inv_mul_cancel₀ hcorr.ne'
        rw [hmul, Real.rpow_one]
  let t₀ : ℝ := min tFar tStrict
  have ht₀ : 0 < t₀ := by dsimp [t₀]; exact lt_min htFar htStrict
  refine ⟨C', t₀, hC', ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall a
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have htFarSmall : t < tFar := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htStrictSmall : t < tStrict := lt_of_lt_of_le htSmall (min_le_right _ _)
  have hpowSmall : t ^ ρ < η := by
    calc
      t ^ ρ < tStrict ^ ρ := Real.rpow_lt_rpow ht.le htStrictSmall hcorr
      _ = η := hStrictPow
  have hcoeffSmall : C' * t ^ ρ < gap / 2 := by
    calc
      C' * t ^ ρ < C' * η := mul_lt_mul_of_pos_left hpowSmall hC'
      _ = gap / 2 := by dsimp [η]; field_simp [hC'.ne'] <;> ring
  have hbetaPow : t ^ β = t ^ α * t ^ ρ := by
    dsimp [β]
    exact Real.rpow_add ht α ρ
  have hrootCoef : (0.7 : ℝ) ^ (1 / 4 : ℝ) + C' * t ^ ρ < 0.8 ^ (1 / 4 : ℝ) := by
    have hgapdef : gap = 0.8 ^ (1 / 4 : ℝ) - 0.7 ^ (1 / 4 : ℝ) := rfl
    linarith [hcoeffSmall, hgapdef]
  have hRootInitial (i : Torus d m) :
      rowL4Root (fun j => normalizedInverse (I.state 0) t i j) ≤
        (0.7 : ℝ) ^ (1 / 4 : ℝ) * t ^ α := by
    have hfourNonneg : 0 ≤ rowFour (normalizedInverse (I.state 0) t) i := by
      unfold rowFour
      positivity
    have hroot := Real.rpow_le_rpow hfourNonneg (I.initialRows i)
      (by norm_num : 0 ≤ (1 / 4 : ℝ))
    have hscale : (0.7 * t ^ (1 + delta)) ^ (1 / 4 : ℝ) =
        (0.7 : ℝ) ^ (1 / 4 : ℝ) * t ^ α := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht.le _)]
      rw [← Real.rpow_mul ht.le]
      congr 1
      dsimp [α]
      ring
    calc
      rowL4Root (fun j => normalizedInverse (I.state 0) t i j) =
          rowFour (normalizedInverse (I.state 0) t) i ^ (1 / 4 : ℝ) := rfl
      _ ≤ (0.7 * t ^ (1 + delta)) ^ (1 / 4 : ℝ) := hroot
      _ = _ := hscale
  have hrowRoot (i : Torus d m) :
      rowL4Root (fun j => normalizedInverse (I.state a) t i j) ≤
        ((0.7 : ℝ) ^ (1 / 4 : ℝ) + C' * t ^ ρ) * t ^ α := by
    let near : Finset (Fin k) := Finset.univ.filter fun q =>
      i ∈ cube d m (I.anchor q) (100 * I.Ds)
    let far : Finset (Fin k) := Finset.univ.filter fun q =>
      i ∉ cube d m (I.anchor q) (100 * I.Ds)
    let prefixOps : Finset (Fin k) := Finset.univ.filter fun q => q.val < a.val
    have hnearCount : (near.card : ℝ) ≤ C * t ^ (-(d : ℝ) * nu d) := by
      simpa [near, hIC] using assembly_near_operation_count I i
    have hincrement (q : Fin k) :
        rowL4Root (fun j => survivorDifference (I.state q.castSucc)
          (I.state q.succ) t i j) ≤ C ^ 4 * t ^ e := by
      simpa [hIC, e] using survivor_increment_l4_bound I q i
    have hpowNear :
        t ^ (-(d : ℝ) * nu d) * t ^ e = t ^ β := by
      calc
        t ^ (-(d : ℝ) * nu d) * t ^ e = t ^ (-(d : ℝ) * nu d + e) := by
          rw [← Real.rpow_add ht]
        _ = t ^ β := by
          apply congrArg (fun x : ℝ => t ^ x)
          linarith [hbetaEq]
    have hnearSum :
        (∑ q ∈ near, rowL4Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) ≤ C ^ 5 * t ^ β := by
      have hincNonneg (q : Fin k) : 0 ≤ rowL4Root (fun j =>
          survivorDifference (I.state q.castSucc) (I.state q.succ) t i j) := by
        unfold rowL4Root
        positivity
      calc
        _ ≤ ∑ q ∈ near, C ^ 4 * t ^ e := Finset.sum_le_sum (fun q hq => hincrement q)
        _ = (near.card : ℝ) * (C ^ 4 * t ^ e) := by simp
        _ ≤ (C * t ^ (-(d : ℝ) * nu d)) * (C ^ 4 * t ^ e) :=
          mul_le_mul_of_nonneg_right hnearCount (by positivity)
        _ = C ^ 5 * (t ^ (-(d : ℝ) * nu d) * t ^ e) := by ring
        _ = C ^ 5 * t ^ β := by rw [hpowNear]
    have hfarSum := hFar m k t b r I hIC hIc hIP htFarSmall i far (by
      intro q hq
      simpa [far] using hq)
    have hsplit :
        (∑ q : Fin k, rowL4Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) =
          (∑ q ∈ near, rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j)) +
          (∑ q ∈ far, rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j)) := by
      simpa [near, far] using
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin k)))
          (p := fun q : Fin k => i ∈ cube d m (I.anchor q) (100 * I.Ds))
          (f := fun q : Fin k => rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j))).symm
    have hprefixLe :
        (∑ q ∈ prefixOps, rowL4Root (fun j => survivorDifference
          (I.state q.castSucc) (I.state q.succ) t i j)) ≤
          C' * t ^ β := by
      have hprefixAll :
          (∑ q ∈ prefixOps, rowL4Root (fun j => survivorDifference
            (I.state q.castSucc) (I.state q.succ) t i j)) ≤
            ∑ q : Fin k, rowL4Root (fun j => survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro q hq hnot
        unfold rowL4Root
        positivity
      calc
        _ ≤ ∑ q : Fin k, rowL4Root (fun j => survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j) := hprefixAll
        _ = (∑ q ∈ near, rowL4Root (fun j => survivorDifference
                (I.state q.castSucc) (I.state q.succ) t i j)) +
              (∑ q ∈ far, rowL4Root (fun j => survivorDifference
                (I.state q.castSucc) (I.state q.succ) t i j)) := hsplit
        _ ≤ C ^ 5 * t ^ β + Kfar * t := add_le_add hnearSum hfarSum
        _ ≤ (C ^ 5 + Kfar) * t ^ β := by
          have htpow : t ≤ t ^ β :=
            by simpa [Real.rpow_one] using
              (Real.rpow_le_rpow_of_exponent_ge ht ht1 hbetaLe)
          have hfar' := mul_le_mul_of_nonneg_left htpow (le_of_lt hKfar)
          nlinarith [hfar']
    by_cases hi : i ∈ (I.state a).active
    · have hroot0 := hRootInitial i
      calc
        rowL4Root (fun j => normalizedInverse (I.state a) t i j) ≤
            rowL4Root (fun j => normalizedInverse (I.state 0) t i j) +
              ∑ q ∈ prefixOps, rowL4Root (fun j => survivorDifference
                (I.state q.castSucc) (I.state q.succ) t i j) :=
                  active_row_l4_prefix_bound I a i hi
        _ ≤ (0.7 : ℝ) ^ (1 / 4 : ℝ) * t ^ α + C' * t ^ β :=
              add_le_add hroot0 hprefixLe
        _ = ((0.7 : ℝ) ^ (1 / 4 : ℝ) + C' * t ^ ρ) * t ^ α := by
              rw [hbetaPow]
              ring
    · have hzero : ∀ j, normalizedInverse (I.state a) t i j = 0 := by
        intro j
        have hs := (I.physical a).2.1 i j (Or.inl hi)
        simp [normalizedInverse, hs]
      simp [rowL4Root, hzero]
      positivity
  refine ⟨?_, ?_⟩
  · intro i
    exact hrowRoot i
  · intro i
    by_cases hi : i ∈ (I.state a).active
    · have hroot := hrowRoot i
      have hstrict := mul_lt_mul_of_pos_right hrootCoef (Real.rpow_pos_of_pos ht α)
      have hrowStrict : rowL4Root (fun j => normalizedInverse (I.state a) t i j) <
          (0.8 : ℝ) ^ (1 / 4 : ℝ) * t ^ α := lt_of_le_of_lt hroot hstrict
      have hfour :
          (rowL4Root (fun j => normalizedInverse (I.state a) t i j)) ^ 4 =
            rowFour (normalizedInverse (I.state a) t) i := by
        simpa [rowFour] using rowL4Root_pow_four
          (fun j => normalizedInverse (I.state a) t i j)
      have hrootNonneg : 0 ≤ rowL4Root (fun j => normalizedInverse (I.state a) t i j) := by
        unfold rowL4Root
        positivity
      have hfourStrict := Real.rpow_lt_rpow hrootNonneg hrowStrict
        (by norm_num : 0 < (4 : ℝ))
      have hfourStrictNat :
          (rowL4Root (fun j => normalizedInverse (I.state a) t i j)) ^ 4 <
            ((0.8 : ℝ) ^ (1 / 4 : ℝ) * t ^ α) ^ 4 := by
        calc
          _ = (rowL4Root (fun j => normalizedInverse (I.state a) t i j)) ^ (4 : ℝ) :=
            (Real.rpow_natCast _ 4).symm
          _ < ((0.8 : ℝ) ^ (1 / 4 : ℝ) * t ^ α) ^ (4 : ℝ) := hfourStrict
          _ = _ := Real.rpow_natCast _ 4
      have hupper :
          ((0.8 : ℝ) ^ (1 / 4 : ℝ) * t ^ α) ^ 4 =
            0.8 * t ^ (1 + delta) := by
        rw [mul_pow]
        have hConst : ((0.8 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 0.8 := by
          calc
            _ = ((0.8 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) :=
              (Real.rpow_natCast _ 4).symm
            _ = 0.8 ^ ((1 / 4 : ℝ) * 4) := (Real.rpow_mul (by norm_num) _ _).symm
            _ = 0.8 := by norm_num [Real.rpow_one]
        have htFourth : (t ^ α) ^ 4 = t ^ (1 + delta) := by
          calc
            (t ^ α) ^ 4 = (t ^ α) ^ (4 : ℝ) := (Real.rpow_natCast _ 4).symm
            _ = t ^ (α * 4) := (Real.rpow_mul ht.le _ _).symm
            _ = t ^ (1 + delta) := by congr 1 <;> dsimp [α] <;> ring
        rw [hConst, htFourth]
      calc
        rowFour (normalizedInverse (I.state a) t) i =
            (rowL4Root (fun j => normalizedInverse (I.state a) t i j)) ^ 4 := hfour.symm
        _ < ((0.8 : ℝ) ^ (1 / 4 : ℝ) * t ^ α) ^ 4 := hfourStrictNat
        _ = 0.8 * t ^ (1 + delta) := hupper
    · have hzero : ∀ j, normalizedInverse (I.state a) t i j = 0 := by
        intro j
        have hs := (I.physical a).2.1 i j (Or.inl hi)
        simp [normalizedInverse, hs]
      simp [rowFour, hzero]
      positivity

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_rowFour_output
