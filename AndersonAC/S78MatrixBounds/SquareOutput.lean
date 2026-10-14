import AndersonAC.S78MatrixBounds.IncrementL2
import AndersonAC.S78MatrixBounds.Schur
import AndersonAC.S78MatrixBounds.RowFourOutput
import AndersonAC.S78MatrixBounds.Ward

open scoped BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

private def activeCompression {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * A *
    Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)

private theorem activeCompression_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (A : Matrix ι ι ℂ) (i j : ι) :
    activeCompression S A i j = if i ∈ S ∧ j ∈ S then A i j else 0 := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [activeCompression, Matrix.mul_apply, Matrix.diagonal_apply, hi, hj]

private theorem normalizedInverse_symmetric {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ)
    (hphys : IsDampedEndpoint s r t) : (normalizedInverse s t).IsSymm := by
  have hg := endpoint_inverse_symmetric s r t hphys
  apply Matrix.IsSymm.ext
  intro i j
  simp only [normalizedInverse, Matrix.smul_apply]
  rw [hg.apply i j]

/-- The active-set square-kernel change has a row and column Schur bound.
The telescoped inverse is compared with the initial inverse compressed to the
surviving active set. -/
theorem assembly_square_kernel_output (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
        (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
        ∀ a : Fin (k + 1),
          matrixNorm (squareKernel (normalizedInverse (I.state a) t)) ≤
            matrixNorm (squareKernel (normalizedInverse (I.state 0) t)) +
              t ^ (0.10 * delta) := by
  obtain ⟨Acoef, Kfar, tInc, hAcoef, hKfar, htInc, hincrement⟩ :=
    assembly_rowL2_increment_sum_bound d hd C c P hC hc hP
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hMargins := assembly_exponent_margins_proof d hd
  let β : ℝ := 0.125 * delta - (d : ℝ) * nu d
  let q : ℝ := 0.10 * delta
  have hβq : q < β := by dsimp [β, q]; exact hMargins.2.2.2.1
  have hq : 0 < q := by dsimp [q, delta]; norm_num
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβqpos : 0 < β - q := by linarith
  have h1q : 0 < 1 - q := by dsimp [q, delta]; norm_num
  let V : ℝ := 2 * C / c
  have hV : 0 < V := by dsimp [V]; positivity
  let ε : ℝ := 1 / (4 * (Real.sqrt V + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεden : 4 * (Real.sqrt V + 1) * ε = 1 := by
    dsimp [ε]
    have hden : 4 * (Real.sqrt V + 1) ≠ 0 := by positivity
    field_simp [hden]
  have hεle : ε ≤ 1 / 4 := by
    have hv := Real.sqrt_nonneg V
    nlinarith [hεden]
  have hcoef : 2 * Real.sqrt V * ε + ε ^ 2 ≤ 1 := by
    have hv := Real.sqrt_nonneg V
    have hterm : 4 * Real.sqrt V * ε ≤ 1 := by nlinarith [hεden]
    have hsq : ε ^ 2 ≤ ε / 4 := by nlinarith [sq_nonneg (ε - 1 / 8)]
    nlinarith
  let θNear : ℝ := ε / (2 * (Acoef + 1))
  let θFar : ℝ := ε / (2 * (Kfar + 1))
  have hθNear : 0 < θNear := by dsimp [θNear]; positivity
  have hθFar : 0 < θFar := by dsimp [θFar]; positivity
  let tNear : ℝ := θNear ^ (1 / (β - q))
  let tFar : ℝ := θFar ^ (1 / (1 - q))
  have htNear : 0 < tNear := by dsimp [tNear]; positivity
  have htFar : 0 < tFar := by dsimp [tFar]; positivity
  have hNearPower : tNear ^ (β - q) = θNear := by
    dsimp [tNear]
    calc
      (θNear ^ (1 / (β - q))) ^ (β - q) =
          θNear ^ ((1 / (β - q)) * (β - q)) :=
            (Real.rpow_mul hθNear.le _ _).symm
      _ = θNear := by
        have hmul : (1 / (β - q)) * (β - q) = 1 := by
          field_simp [hβqpos.ne']
        rw [hmul, Real.rpow_one]
  have hFarPower : tFar ^ (1 - q) = θFar := by
    dsimp [tFar]
    calc
      (θFar ^ (1 / (1 - q))) ^ (1 - q) =
          θFar ^ ((1 / (1 - q)) * (1 - q)) :=
            (Real.rpow_mul hθFar.le _ _).symm
      _ = θFar := by
        have hmul : (1 / (1 - q)) * (1 - q) = 1 := by
          field_simp [h1q.ne']
        rw [hmul, Real.rpow_one]
  let t₀ : ℝ := min tInc (min tNear tFar)
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact lt_min htInc (lt_min htNear htFar)
  refine ⟨t₀, ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP htSmall a
  rcases I.positive with ⟨ht, ht1, hb, hbt, hcI, hCI, hPI⟩
  have htIncSmall : t < tInc := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htLast : t < min tNear tFar := lt_of_lt_of_le htSmall (min_le_right _ _)
  have htNearSmall : t < tNear := lt_of_lt_of_le htLast (min_le_left _ _)
  have htFarSmall : t < tFar := lt_of_lt_of_le htLast (min_le_right _ _)
  let S := (I.state a).active
  let H0 := normalizedInverse (I.state 0) t
  let Ha := normalizedInverse (I.state a) t
  let Base := activeCompression S H0
  let Diff := Ha - Base
  let prefixOps : Finset (Fin k) := Finset.univ.filter fun q => q.val < a.val
  have hW : Acoef * t ^ β + Kfar * t ≤ ε * t ^ q := by
    have hpowNear : t ^ β = t ^ q * t ^ (β - q) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hpowFar : t = t ^ q * t ^ (1 - q) := by
      calc
        t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ = t ^ q * t ^ (1 - q) := by
          rw [← Real.rpow_add ht]
          congr 1
          ring
    have hpowNearMul : Acoef * t ^ β = Acoef * (t ^ q * t ^ (β - q)) :=
      congrArg (fun x : ℝ => Acoef * x) hpowNear
    have hpowFarMul : Kfar * t = Kfar * (t ^ q * t ^ (1 - q)) :=
      congrArg (fun x : ℝ => Kfar * x) hpowFar
    have hsmallNear : t ^ (β - q) < θNear := by
      calc
        t ^ (β - q) < tNear ^ (β - q) := Real.rpow_lt_rpow ht.le htNearSmall hβqpos
        _ = θNear := hNearPower
    have hsmallFar : t ^ (1 - q) < θFar := by
      calc
        t ^ (1 - q) < tFar ^ (1 - q) := Real.rpow_lt_rpow ht.le htFarSmall h1q
        _ = θFar := hFarPower
    have hnearTerm : Acoef * t ^ (β - q) ≤ ε / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsmallNear.le hAcoef
      have hratio : Acoef * θNear ≤ ε / 2 := by
        dsimp [θNear]
        have hden : 0 < 2 * (Acoef + 1) := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).2
        nlinarith [hAcoef, hε]
      exact hmul.trans hratio
    have hfarTerm : Kfar * t ^ (1 - q) ≤ ε / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsmallFar.le hKfar.le
      have hratio : Kfar * θFar ≤ ε / 2 := by
        dsimp [θFar]
        have hden : 0 < 2 * (Kfar + 1) := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).2
        nlinarith [hKfar.le, hε]
      exact hmul.trans hratio
    calc
      Acoef * t ^ β + Kfar * t =
          Acoef * (t ^ q * t ^ (β - q)) +
            Kfar * (t ^ q * t ^ (1 - q)) := by
              rw [hpowNearMul, hpowFarMul]
      _ = t ^ q * (Acoef * t ^ (β - q) + Kfar * t ^ (1 - q)) := by ring
        _ ≤ t ^ q * ε := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
          linarith
      _ = ε * t ^ q := by ring
  have hbaseEntry (i j : Torus d m) :
      Base i j = if i ∈ S ∧ j ∈ S then H0 i j else 0 := by
    simpa [Base, H0, S] using activeCompression_apply S H0 i j
  have hBaseRow (i : Torus d m) (hi : i ∈ S) : rowTwo Base i ≤ V := by
    have hpoint (j : Torus d m) : ‖Base i j‖ ^ 2 ≤ ‖H0 i j‖ ^ 2 := by
      rw [hbaseEntry]
      by_cases hj : j ∈ S <;> simp [hi, hj]
    have hi0 : i ∈ (I.state 0).active := active_initial_of_active I a i hi
    have hward := endpoint_rowTwo_le_diagonal_im (I.state 0) r t c ht hc
      (by intro j; simpa [hIc] using (I.damping j).1) (I.physical 0)
    have hrow0 : rowTwo H0 i ≤ ((I.state 0).g i i).im / c := by
      simpa [H0] using hward i hi0
    have hlag := I.initialLag i hi0
    have hpowLag : t ^ (0.42 * delta) ≤ 1 := by
      have hp : 0 ≤ 0.42 * delta := by dsimp [delta]; positivity
      have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hp
      simpa using h
    have hImDiff : ((I.state 0).g i i).im ≤ (r i).im +
        ‖(I.state 0).g i i - r i‖ := by
      have hAbs := (Complex.abs_im_le_norm ((I.state 0).g i i - r i))
      have hle := (le_abs_self (((I.state 0).g i i - r i).im)).trans hAbs
      rw [Complex.sub_im] at hle
      linarith
    have hrUpper : (r i).im ≤ C := by simpa [hIC] using (I.damping i).2.1
    have hdiag : ((I.state 0).g i i).im ≤ 2 * C := by
      have hlagC : ‖(I.state 0).g i i - r i‖ ≤ C * t ^ (0.42 * delta) := by
        simpa [hIC] using hlag
      have hlag' : ‖(I.state 0).g i i - r i‖ ≤ C := by
        calc
          _ ≤ C * t ^ (0.42 * delta) := hlagC
          _ ≤ C := by
            calc
              C * t ^ (0.42 * delta) ≤ C * 1 :=
                mul_le_mul_of_nonneg_left hpowLag (by linarith [hC])
              _ = C := by ring
      linarith
    have hrowTwoBound : rowTwo H0 i ≤ V := by
      dsimp [V]
      exact hrow0.trans (div_le_div_of_nonneg_right hdiag hc.le)
    calc
      rowTwo Base i = ∑ j, ‖Base i j‖ ^ 2 := rfl
      _ ≤ ∑ j, ‖H0 i j‖ ^ 2 := Finset.sum_le_sum fun j hj => hpoint j
      _ = rowTwo H0 i := rfl
      _ ≤ V := hrowTwoBound
  have hDiffRowRoot (i : Torus d m) :
      rowL2Root (fun j => Diff i j) ≤ Acoef * t ^ β + Kfar * t := by
    by_cases hi : i ∈ S
    · have hDiffRow : (fun j => Diff i j) =
          (fun j => if j ∈ S then
            ∑ q ∈ prefixOps, survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j else 0) := by
        funext j
        by_cases hj : j ∈ S
        · have htel := normalizedInverse_telescopes_active I a i j hi hj
          dsimp [Diff]
          change Ha i j - Base i j = _
          have hbase : Base i j = H0 i j := by simpa [hi, hj] using hbaseEntry i j
          rw [hbase]
          simp only [if_pos hj]
          dsimp [Ha, H0]
          rw [htel]
          ring
        · have hsupp := (I.physical a).2.1 i j (Or.inr hj)
          have hbaseZero : Base i j = 0 := by simpa [hj] using hbaseEntry i j
          have hHaZero : Ha i j = 0 := by
            simpa [Ha, normalizedInverse] using
              congrArg (fun z : ℂ => (Real.sqrt t : ℂ) * z) hsupp
          simp [Diff, hbaseZero, hHaZero, hj]
      rw [hDiffRow]
      calc
        rowL2Root (fun j => if j ∈ S then
            ∑ q ∈ prefixOps, survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j else 0) ≤
            rowL2Root (fun j => ∑ q ∈ prefixOps, survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j) :=
                rowL2Root_mask_le S _
        _ ≤ ∑ q ∈ prefixOps, rowL2Root (fun j => survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j) :=
                rowL2Root_sum_le prefixOps (fun q j => survivorDifference
                  (I.state q.castSucc) (I.state q.succ) t i j)
        _ ≤ ∑ q : Fin k, rowL2Root (fun j => survivorDifference
              (I.state q.castSucc) (I.state q.succ) t i j) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro q hq hqnot
                exact rowL2Root_nonneg _
        _ ≤ Acoef * t ^ β + Kfar * t := hincrement m k t b r I hIC hIc hIP htIncSmall i
    · have hsupp := (I.physical a).2.1
      have hzero : ∀ j, Ha i j = 0 := by
        intro j
        have h := hsupp i j (Or.inl hi)
        simpa [Ha, normalizedInverse] using
          congrArg (fun z : ℂ => (Real.sqrt t : ℂ) * z) h
      have hbasezero : ∀ j, Base i j = 0 := by
        intro j
        rw [hbaseEntry]
        simp [hi]
      have hrowzero : ∀ j, Diff i j = 0 := by
        intro j
        simp [Diff, hzero j, hbasezero j]
      simp [rowL2Root, hrowzero]
      positivity
  let E : Matrix (Torus d m) (Torus d m) ℂ :=
    squareKernel (Base + Diff) - squareKernel Base
  have hHaEq : Base + Diff = Ha := by
    ext i j
    simp [Diff]
  have hErow (i : Torus d m) :
      (∑ j, ‖E i j‖) ≤ 2 * Real.sqrt V * (Acoef * t ^ β + Kfar * t) +
        (Acoef * t ^ β + Kfar * t) ^ 2 := by
    have hBaseRowAll : rowTwo Base i ≤ V := by
      by_cases hi : i ∈ S
      · exact hBaseRow i hi
      · have hz : ∀ j, Base i j = 0 := by
          intro j
          rw [hbaseEntry]
          simp [hi]
        rw [rowTwo]
        simp [hz, V]
        positivity
    have hWnonneg : 0 ≤ Acoef * t ^ β + Kfar * t := by positivity
    have hrowChange := squareKernel_change_row_sum_bound Base Diff i V
      (Acoef * t ^ β + Kfar * t) hV.le hWnonneg hBaseRowAll (hDiffRowRoot i)
    simpa [E] using hrowChange
  have hHaSymm : Ha.IsSymm := by
    simpa [Ha] using normalizedInverse_symmetric (I.state a) r t (I.physical a)
  have hH0Symm : H0.IsSymm := by
    simpa [H0] using normalizedInverse_symmetric (I.state 0) r t (I.physical 0)
  have hBaseSymm : Base.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    rw [hbaseEntry i j, hbaseEntry j i]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hi, hj, hH0Symm.apply i j]
  have hEsymm : E.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [E, Matrix.sub_apply, squareKernel]
    rw [hHaEq]
    simp [hHaSymm.apply i j, hBaseSymm.apply i j]
  have hrowBound :
      2 * Real.sqrt V * (Acoef * t ^ β + Kfar * t) +
        (Acoef * t ^ β + Kfar * t) ^ 2 ≤ t ^ q := by
    have hWnonneg : 0 ≤ Acoef * t ^ β + Kfar * t := by positivity
    have htq0 : 0 ≤ t ^ q := Real.rpow_nonneg ht.le _
    have htq1 : t ^ q ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 (le_of_lt hq)
      simpa using h
    have hWsmall : Acoef * t ^ β + Kfar * t ≤ ε * t ^ q := hW
    have hWsq : (Acoef * t ^ β + Kfar * t) ^ 2 ≤ (ε * t ^ q) ^ 2 :=
      (sq_le_sq₀ hWnonneg (mul_nonneg hε.le htq0)).2 hWsmall
    calc
      _ ≤ 2 * Real.sqrt V * (ε * t ^ q) + (ε * t ^ q) ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hWsmall (by positivity)) hWsq
      _ ≤ (2 * Real.sqrt V * ε + ε ^ 2) * t ^ q := by
        have hsqPow : (ε * t ^ q) ^ 2 = ε ^ 2 * (t ^ q) ^ 2 := by ring
        rw [hsqPow]
        have hxx : (t ^ q) ^ 2 ≤ t ^ q := by
          rw [pow_two]
          simpa [mul_one] using mul_le_mul_of_nonneg_left htq1 htq0
        calc
          2 * Real.sqrt V * (ε * t ^ q) + ε ^ 2 * (t ^ q) ^ 2 =
              2 * Real.sqrt V * ε * t ^ q + ε ^ 2 * (t ^ q) ^ 2 := by ring
          _ ≤ 2 * Real.sqrt V * ε * t ^ q + ε ^ 2 * t ^ q :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hxx (sq_nonneg ε))
          _ = (2 * Real.sqrt V * ε + ε ^ 2) * t ^ q := by ring
      _ ≤ t ^ q := by simpa using mul_le_mul_of_nonneg_right hcoef htq0
  have hcolBound (j : Torus d m) : (∑ i, ‖E i j‖) ≤ t ^ q := by
    calc
      (∑ i, ‖E i j‖) = ∑ i, ‖E j i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hEsymm.apply i j]
      _ ≤ t ^ q := (hErow j).trans hrowBound
  have hE0 : 0 ≤ t ^ q := Real.rpow_nonneg ht.le _
  have hEnorm : matrixNorm E ≤ t ^ q := by
    have hrowTo (i : Torus d m) : (∑ j, ‖E i j‖) ≤ t ^ q :=
      (hErow i).trans hrowBound
    have hschur := euclidean_schur_bound E (t ^ q) (t ^ q) hE0 hE0 hrowTo hcolBound
    calc
      matrixNorm E ≤ Real.sqrt (t ^ q * t ^ q) := hschur
      _ = t ^ q := by
        calc
          Real.sqrt (t ^ q * t ^ q) = Real.sqrt ((t ^ q) ^ 2) := by congr 1 <;> ring
          _ = |t ^ q| := Real.sqrt_sq_eq_abs _
          _ = t ^ q := abs_of_nonneg hE0
  have hSqEq : squareKernel Ha = squareKernel Base + E := by
    ext i j
    simp [E, hHaEq, squareKernel]
  have htriangle : matrixNorm (squareKernel Ha) ≤
      matrixNorm (squareKernel Base) + matrixNorm E := by
    rw [hSqEq]
    change ‖Matrix.toEuclideanCLM (n := Torus d m) (𝕜 := ℂ)
      (squareKernel Base + E)‖ ≤ _
    calc
      _ = ‖Matrix.toEuclideanCLM (n := Torus d m) (𝕜 := ℂ) (squareKernel Base) +
            Matrix.toEuclideanCLM (n := Torus d m) (𝕜 := ℂ) E‖ := by simp
      _ ≤ _ := norm_add_le _ _
  have hBaseSquare : squareKernel Base = activeCompression S (squareKernel H0) := by
    ext i j
    rw [activeCompression_apply]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [squareKernel, hbaseEntry, hi, hj]
  have hcompress : matrixNorm (squareKernel Base) ≤ matrixNorm (squareKernel H0) := by
    rw [hBaseSquare]
    simpa [activeCompression] using matrixNorm_compress_le (squareKernel H0) S
  calc
    matrixNorm (squareKernel Ha) ≤ matrixNorm (squareKernel Base) + matrixNorm E := htriangle
    _ ≤ matrixNorm (squareKernel H0) + t ^ q := add_le_add hcompress hEnorm
    _ = matrixNorm (squareKernel (normalizedInverse (I.state 0) t)) +
          t ^ (0.10 * delta) := by rfl

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_square_kernel_output
