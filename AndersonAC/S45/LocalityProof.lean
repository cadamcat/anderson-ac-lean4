import AndersonAC.S45.Definitions
import AndersonAC.S45.GammaProof
import AndersonAC.S45.PrestateProof
import AndersonAC.S45.SingleDeletionProof
import AndersonAC.S45.RecordsProof

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder
namespace AndersonAC.AgentS45
open AndersonAC.S45

private def euclCLM {ι : Type*} [Fintype ι] [DecidableEq ι] (A : CMat ι) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun A

lemma damped_inner_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CMat ι) (hR : R.IsHermitian) (τ : ι → ℝ)
    (x : EuclideanSpace ℂ ι) :
    Complex.im (inner ℂ x (euclCLM
      (R - diagonal (fun i => Complex.I * (τ i : ℂ))) x)) =
      -∑ i, τ i * ‖x i‖ ^ 2 := by
  let v : ι → ℂ := x.ofLp
  have hreal : (star v ⬝ᵥ R *ᵥ v).im = 0 := by
    have h := hR.star_dotProduct_mulVec_comm v v
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    nlinarith
  have hdiag : (star v ⬝ᵥ diagonal (fun i => Complex.I * (τ i : ℂ)) *ᵥ v).im =
      ∑ i, τ i * ‖v i‖ ^ 2 := by
    simp only [Matrix.mulVec_diagonal, dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq, Complex.normSq_apply]
    ring
  have hinner :
      inner ℂ x (euclCLM
        (R - diagonal (fun i => Complex.I * (τ i : ℂ))) x) =
        star v ⬝ᵥ (R - diagonal (fun i => Complex.I * (τ i : ℂ))) *ᵥ v := by
    have hx : (WithLp.toLp 2 v : EuclideanSpace ℂ ι) = x := by simp [v]
    rw [← hx]
    change inner ℂ (WithLp.toLp 2 v)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (R - diagonal (fun i => Complex.I * (τ i : ℂ))) (WithLp.toLp 2 v)) = _
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm]
  rw [hinner, sub_mulVec, dotProduct_sub, Complex.sub_im, hreal, hdiag]
  simp [v]

lemma damped_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CMat ι) (hR : R.IsHermitian) (τ : ι → ℝ) (b : ℝ)
    (hb : 0 < b) (hτ : ∀ i, b ≤ τ i) (x : EuclideanSpace ℂ ι) :
    b * ‖x‖ ≤ ‖euclCLM (R - diagonal (fun i => Complex.I * (τ i : ℂ))) x‖ := by
  have hsum : b * ‖x‖ ^ 2 ≤ ∑ i, τ i * ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      b * ∑ i, ‖x i‖ ^ 2 = ∑ i, b * ‖x i‖ ^ 2 := by simp [Finset.mul_sum]
      _ ≤ ∑ i, τ i * ‖x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hτ i) (sq_nonneg ‖x i‖)
  have hsum_non : 0 ≤ ∑ i, τ i * ‖x i‖ ^ 2 :=
    le_trans (mul_nonneg hb.le (sq_nonneg ‖x‖)) hsum
  have hinner_lower :
      b * ‖x‖ ^ 2 ≤ ‖inner ℂ x
        (euclCLM (R - diagonal (fun i => Complex.I * (τ i : ℂ))) x)‖ := by
    calc
      b * ‖x‖ ^ 2 ≤ ∑ i, τ i * ‖x i‖ ^ 2 := hsum
      _ = |(inner ℂ x
          (euclCLM (R - diagonal (fun i => Complex.I * (τ i : ℂ))) x)).im| := by
        rw [damped_inner_im R hR τ x]
        simp [abs_of_nonneg hsum_non]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hprod := hinner_lower.trans (norm_inner_le_norm _ _)
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply (mul_le_mul_iff_left₀ hxpos).mp
    nlinarith [hprod]

lemma damped_unit_inv_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CMat ι) (hR : R.IsHermitian) (τ : ι → ℝ) (b : ℝ)
    (hb : 0 < b) (hτ : ∀ i, b ≤ τ i) :
    IsUnit (R - diagonal (fun i => Complex.I * (τ i : ℂ))) ∧
      ‖(R - diagonal (fun i => Complex.I * (τ i : ℂ)))⁻¹‖ ≤ b⁻¹ := by
  let M : CMat ι := R - diagonal (fun i => Complex.I * (τ i : ℂ))
  have hzero (v : ι → ℂ) (hv : M *ᵥ v = 0) : v = 0 := by
    have h := damped_lower R hR τ b hb hτ (WithLp.toLp 2 v)
    have hMv : euclCLM M (WithLp.toLp 2 v) = 0 := by
      change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M (WithLp.toLp 2 v)) = 0
      rw [Matrix.toEuclideanCLM_toLp, hv]
      simp
    rw [hMv, norm_zero] at h
    have hnorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 0 := by
      have hnn := norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
      nlinarith
    have hto : (WithLp.toLp 2 v : EuclideanSpace ℂ ι) = 0 := norm_eq_zero.mp hnorm
    ext i
    have hi := congrArg (fun z : EuclideanSpace ℂ ι => z.ofLp i) hto
    simpa using hi
  have hinj : Function.Injective M.mulVec := by
    intro v w hvw
    have h := hzero (v - w) (by simpa [Matrix.mulVec_sub, hvw])
    exact sub_eq_zero.mp h
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hunit
  have hmul : M * M⁻¹ = 1 := by
    simpa [M] using Matrix.mul_nonsing_inv_cancel_right (A := M) (B := (1 : CMat ι)) hdet
  have hclm : ‖euclCLM (M⁻¹)‖ ≤ b⁻¹ := by
    refine (euclCLM (M⁻¹)).opNorm_le_bound (inv_nonneg.mpr hb.le) ?_
    intro y
    let v := M⁻¹ *ᵥ y.ofLp
    have hMv : M *ᵥ v = y.ofLp := by
      dsimp [v]
      rw [Matrix.mulVec_mulVec, hmul]
      simp
    have hlow := damped_lower R hR τ b hb hτ (WithLp.toLp 2 v)
    have happly : euclCLM (M⁻¹) y = WithLp.toLp 2 v := by
      have hy : (WithLp.toLp 2 y.ofLp : EuclideanSpace ℂ ι) = y := by simp
      rw [← hy]
      change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M⁻¹
        (WithLp.toLp 2 y.ofLp)) = WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp)
      rw [Matrix.toEuclideanCLM_toLp]

    have hbound : b * ‖euclCLM (M⁻¹) y‖ ≤ ‖y‖ := by
      have hlow' : b * ‖WithLp.toLp 2 v‖ ≤ ‖euclCLM M (WithLp.toLp 2 v)‖ := by
        simpa [M, euclCLM, Matrix.toEuclideanCLM_toLp] using hlow
      change b * ‖WithLp.toLp 2 v‖ ≤ ‖WithLp.toLp 2 (M *ᵥ v)‖ at hlow'
      rw [hMv] at hlow'
      simpa [happly] using hlow'
    calc
      ‖euclCLM (M⁻¹) y‖ ≤ ‖y‖ / b := (le_div_iff₀ hb).2 (by simpa [mul_comm] using hbound)
      _ = b⁻¹ * ‖y‖ := by rw [div_eq_mul_inv]; ring
  have hnorm : ‖M⁻¹‖ = ‖euclCLM (M⁻¹)‖ := by
    change ‖M⁻¹‖ =
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun (M⁻¹)‖
    exact (Matrix.l2_opNorm_toEuclideanCLM (M⁻¹)).symm
  constructor
  · simpa [M] using hunit
  · simpa [hnorm, M] using hclm

private def collapsedNatDistance {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (i j : ι) : ℕ :=
  sInf {m : ℕ | ∃ w : G.Walk i j, walkCost G T w = m}

private lemma walkCost_append {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) {i j k : ι}
    (p : G.Walk i j) (q : G.Walk j k) :
    walkCost G T (p.append q) = walkCost G T p + walkCost G T q := by
  induction p with
  | nil => simp [walkCost, SimpleGraph.Walk.append]
  | cons h p ih => simp [walkCost, SimpleGraph.Walk.append, ih, Nat.add_assoc]

private lemma collapsedNat_attained {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) (i j : ι) :
    ∃ w : G.Walk i j, walkCost G T w = collapsedNatDistance G T i j := by
  have hn : {m : ℕ | ∃ w : G.Walk i j, walkCost G T w = m}.Nonempty := by
    rcases hconn.preconnected i j with ⟨w⟩
    exact ⟨walkCost G T w, ⟨w, rfl⟩⟩
  rcases Nat.sInf_mem hn with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  simpa [collapsedNatDistance] using hw

private lemma collapsedNat_le_walk {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) {i j : ι} (w : G.Walk i j) :
    collapsedNatDistance G T i j ≤ walkCost G T w :=
  Nat.sInf_le ⟨w, rfl⟩

private lemma collapsedNat_triangle {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) (i j k : ι) :
    collapsedNatDistance G T i k ≤
      collapsedNatDistance G T i j + collapsedNatDistance G T j k := by
  rcases collapsedNat_attained G T hconn i j with ⟨p, hp⟩
  rcases collapsedNat_attained G T hconn j k with ⟨q, hq⟩
  have h := collapsedNat_le_walk G T (p.append q)
  rw [walkCost_append G T p q, hp, hq] at h
  exact h

private lemma collapsed_eq_nat {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) (i j : ι) :
    collapsedDistance G T i j = (collapsedNatDistance G T i j : ℝ) := by
  have hn : {m : ℕ | ∃ w : G.Walk i j, walkCost G T w = m}.Nonempty := by
    rcases hconn.preconnected i j with ⟨w⟩
    exact ⟨walkCost G T w, ⟨w, rfl⟩⟩
  rcases Nat.sInf_mem hn with ⟨w, hw⟩
  have hs : {a : ℝ | ∃ w : G.Walk i j, a = (walkCost G T w : ℝ)}.Nonempty := by
    refine ⟨(walkCost G T w : ℝ), ?_⟩
    exact ⟨w, rfl⟩
  have hb : BddBelow {a : ℝ | ∃ w : G.Walk i j, a = (walkCost G T w : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro a ⟨p, rfl⟩
    exact_mod_cast Nat.zero_le (walkCost G T p)
  unfold collapsedDistance
  apply le_antisymm
  · exact csInf_le hb ⟨w, by exact_mod_cast hw.symm⟩
  · apply le_csInf hs
    intro a ha
    rcases ha with ⟨p, rfl⟩
    exact_mod_cast (show collapsedNatDistance G T i j ≤ walkCost G T p from
      collapsedNat_le_walk G T p)

private lemma collapsed_triangle {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) (i j k : ι) :
    collapsedDistance G T i k ≤ collapsedDistance G T i j + collapsedDistance G T j k := by
  rw [collapsed_eq_nat G T hconn i k, collapsed_eq_nat G T hconn i j,
    collapsed_eq_nat G T hconn j k]
  exact_mod_cast collapsedNat_triangle G T hconn i j k

private lemma collapsedNat_edge_le {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) {i j : ι} (hij : G.Adj i j) :
    collapsedNatDistance G T i j ≤ if i ∈ T ∨ j ∈ T then 0 else 1 := by
  have h := collapsedNat_le_walk G T (SimpleGraph.Walk.cons hij SimpleGraph.Walk.nil)
  simpa [walkCost] using h

private lemma collapsed_edge_le {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) {i j : ι}
    (hij : G.Adj i j) :
    collapsedDistance G T i j ≤ (if i ∈ T ∨ j ∈ T then (0 : ℝ) else 1) := by
  rw [collapsed_eq_nat G T hconn i j]
  exact_mod_cast collapsedNat_edge_le G T hij

private lemma collapsed_self_eq_zero {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) (i : ι) :
    collapsedDistance G T i i = 0 := by
  rw [collapsed_eq_nat G T hconn i i]
  have h := collapsedNat_le_walk G T (SimpleGraph.Walk.nil : G.Walk i i)
  simp [walkCost] at h
  exact_mod_cast h

private lemma collapsed_edge_zero {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) {i j : ι}
    (hij : G.Adj i j) (hterm : i ∈ T ∨ j ∈ T) :
    collapsedDistance G T i j = 0 := by
  have hnat := collapsedNat_edge_le G T hij
  rw [if_pos hterm] at hnat
  have hz : collapsedNatDistance G T i j = 0 := Nat.eq_zero_of_le_zero hnat
  rw [collapsed_eq_nat G T hconn i j, hz]
  simp

private lemma collapsed_adj_eq_terminal {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) {i j z : ι}
    (hij : G.Adj i j) (hterm : i ∈ T ∨ j ∈ T) :
    collapsedDistance G T i z = collapsedDistance G T j z := by
  have hzero₁ := collapsed_edge_zero G T hconn hij hterm
  have hzero₂ := collapsed_edge_zero G T hconn hij.symm (Or.symm hterm)
  apply le_antisymm
  · calc
      collapsedDistance G T i z ≤ collapsedDistance G T i j + collapsedDistance G T j z :=
        collapsed_triangle G T hconn i j z
      _ = collapsedDistance G T j z := by rw [hzero₁]; simp
  · calc
      collapsedDistance G T j z ≤ collapsedDistance G T j i + collapsedDistance G T i z :=
        collapsed_triangle G T hconn j i z
      _ = collapsedDistance G T i z := by rw [hzero₂]; simp

private lemma collapsed_adj_diff_le_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (T : Finset ι) (hconn : G.Connected) {i j z : ι}
    (hij : G.Adj i j) (hi : i ∉ T) (hj : j ∉ T) :
    |collapsedDistance G T i z - collapsedDistance G T j z| ≤ 1 := by
  have h₁ : collapsedDistance G T i z ≤ collapsedDistance G T j z + 1 := by
    have he := collapsed_edge_le G T hconn hij
    have he' : collapsedDistance G T i j ≤ 1 := by simpa [hi, hj] using he
    linarith [collapsed_triangle G T hconn i j z]
  have h₂ : collapsedDistance G T j z ≤ collapsedDistance G T i z + 1 := by
    have he := collapsed_edge_le G T hconn hij.symm
    have he' : collapsedDistance G T j i ≤ 1 := by simpa [hi, hj] using he
    linarith [collapsed_triangle G T hconn j i z]
  rw [abs_le]
  constructor <;> linarith

private lemma matrix_schur_opNorm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMat ι) (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ r) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (r * c) := by
  have hraw (v : ι → ℂ) :
      ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ r * c * ∑ j, ‖v j‖ ^ 2 := by
    have hrow_i (i : ι) :
        ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
      have hnorm : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
        simp only [Matrix.mulVec_apply]
        calc
          ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
          _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp [norm_mul]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun j => ‖A i j‖ * ‖v j‖)
        (f := fun j => ‖A i j‖)
        (g := fun j => ‖A i j‖ * ‖v j‖ ^ 2)
        (by intro j hj; positivity)
        (by intro j hj; positivity)
        (by intro j hj; ring_nf; exact le_rfl)
      calc
        ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
        _ ≤ _ := hcs
    calc
      ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ ∑ i, r * (∑ j, ‖A i j‖ * ‖v j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact (hrow_i i).trans <| mul_le_mul_of_nonneg_right (hrow i) (by positivity)
      _ = r * ∑ j, (∑ i, ‖A i j‖) * ‖v j‖ ^ 2 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext j
        rw [← Finset.mul_sum, Finset.sum_mul]
      _ ≤ r * ∑ j, c * ‖v j‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hr
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg ‖v j‖)
      _ = r * c * ∑ j, ‖v j‖ ^ 2 := by
        calc
          r * ∑ j, c * ‖v j‖ ^ 2 = r * (c * ∑ j, ‖v j‖ ^ 2) := by
            congr 1
            rw [← Finset.mul_sum]
          _ = r * c * ∑ j, ‖v j‖ ^ 2 := by ring
  have hvec (x : EuclideanSpace ℂ ι) :
      ‖euclCLM A x‖ ≤ Real.sqrt (r * c) * ‖x‖ := by
    have hsq : ‖euclCLM A x‖ ^ 2 ≤ r * c * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      change ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ r * c * ∑ i, ‖x.ofLp i‖ ^ 2
      exact hraw x.ofLp
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hr hc)]
    exact hsq
  have hclm := (euclCLM A).opNorm_le_bound (M := Real.sqrt (r * c))
    (Real.sqrt_nonneg _) hvec
  have hnorm : ‖A‖ = ‖euclCLM A‖ := by
    change ‖A‖ = ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun A‖
    exact (Matrix.l2_opNorm_toEuclideanCLM A).symm
  rw [hnorm]
  exact hclm

private lemma sparse_matrix_row_col_sum {P I : Type*} [Fintype P] [DecidableEq P]
    [Fintype I] [DecidableEq I] (G : SimpleGraph I) [DecidableRel G.Adj] (site : P → I)
    (hsite : Function.Injective site) (d : ℕ)
    (hdegree : ∀ i, (Finset.univ.filter (G.Adj i)).card ≤ 2 * d)
    (A : CMat P) (ε : ℝ) (hε : 0 ≤ ε)
    (hentry : ∀ i j, ‖A i j‖ ≤ ε) (hdiag : ∀ i, A i i = 0)
    (hzero : ∀ i j, i ≠ j → ¬ G.Adj (site i) (site j) → A i j = 0) :
    (∀ i, ∑ j, ‖A i j‖ ≤ (2 * (d : ℝ)) * ε) ∧
      (∀ j, ∑ i, ‖A i j‖ ≤ (2 * (d : ℝ)) * ε) := by
  classical
  classical
  let e : P ↪ I := ⟨site, hsite⟩
  constructor
  · intro i
    let S : Finset P := Finset.univ.filter (fun j => G.Adj (site i) (site j))
    let N : Finset I := Finset.univ.filter (G.Adj (site i))
    have hmap : S.map e ⊆ N := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hcard : S.card ≤ 2 * d := by
      calc
        S.card = (S.map e).card := by simp [e]
        _ ≤ N.card := Finset.card_le_card hmap
        _ ≤ 2 * d := hdegree (site i)
    have hsum : (∑ j, ‖A i j‖) = ∑ j ∈ S, ‖A i j‖ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      by_cases hij : i = j
      · subst j
        simp [hdiag]
      · have hAdj : ¬ G.Adj (site i) (site j) := by
          intro hAdj
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj⟩)
        simp [hzero i j hij hAdj]
    calc
      ∑ j, ‖A i j‖ = ∑ j ∈ S, ‖A i j‖ := hsum
      _ ≤ (S.card : ℝ) * ε := by
        simpa [nsmul_eq_mul, mul_comm] using
          (Finset.sum_le_card_nsmul S (fun j => ‖A i j‖) ε fun j hj => hentry i j)
      _ ≤ (2 * (d : ℝ)) * ε := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε
  · intro j
    let S : Finset P := Finset.univ.filter (fun i => G.Adj (site i) (site j))
    let N : Finset I := Finset.univ.filter (G.Adj (site j))
    have hmap : S.map e ⊆ N := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.symm⟩
    have hcard : S.card ≤ 2 * d := by
      calc
        S.card = (S.map e).card := by simp [e]
        _ ≤ N.card := Finset.card_le_card hmap
        _ ≤ 2 * d := hdegree (site j)
    have hsum : (∑ i, ‖A i j‖) = ∑ i ∈ S, ‖A i j‖ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      by_cases hij : i = j
      · subst i
        simp [hdiag]
      · have hAdj : ¬ G.Adj (site i) (site j) := by
          intro hAdj
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj⟩)
        simp [hzero i j hij hAdj]
    calc
      ∑ i, ‖A i j‖ = ∑ i ∈ S, ‖A i j‖ := hsum
      _ ≤ (S.card : ℝ) * ε := by
        simpa [nsmul_eq_mul, mul_comm] using
          (Finset.sum_le_card_nsmul S (fun i => ‖A i j‖) ε fun i hi => hentry i j)
      _ ≤ (2 * (d : ℝ)) * ε := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε

private lemma matrix_lower_inverse_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CMat ι) (b : ℝ) (hb : 0 < b)
    (hlower : ∀ x, b * ‖x‖ ≤ ‖euclCLM M x‖) :
    IsUnit M ∧ ‖M⁻¹‖ ≤ b⁻¹ := by
  have hzero (v : ι → ℂ) (hv : M *ᵥ v = 0) : v = 0 := by
    have h := hlower (WithLp.toLp 2 v)
    have hMv : euclCLM M (WithLp.toLp 2 v) = 0 := by
      change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M (WithLp.toLp 2 v)) = 0
      rw [Matrix.toEuclideanCLM_toLp, hv]
      simp
    rw [hMv, norm_zero] at h
    have hnorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 0 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
    have hto : (WithLp.toLp 2 v : EuclideanSpace ℂ ι) = 0 := norm_eq_zero.mp hnorm
    ext i
    have hi := congrArg (fun z : EuclideanSpace ℂ ι => z.ofLp i) hto
    simpa using hi
  have hinj : Function.Injective M.mulVec := by
    intro v w hvw
    have h := hzero (v - w) (by simpa [Matrix.mulVec_sub, hvw])
    exact sub_eq_zero.mp h
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hunit
  have hmul : M * M⁻¹ = 1 := by
    simpa using Matrix.mul_nonsing_inv_cancel_right (A := M) (B := (1 : CMat ι)) hdet
  have hclm : ‖euclCLM (M⁻¹)‖ ≤ b⁻¹ := by
    refine (euclCLM (M⁻¹)).opNorm_le_bound (M := b⁻¹) (inv_nonneg.mpr hb.le) ?_
    intro y
    let v := M⁻¹ *ᵥ y.ofLp
    have hMv : M *ᵥ v = y.ofLp := by
      dsimp [v]
      rw [Matrix.mulVec_mulVec, hmul]
      simp
    have happly : euclCLM (M⁻¹) y = WithLp.toLp 2 v := by
      have hy : (WithLp.toLp 2 y.ofLp : EuclideanSpace ℂ ι) = y := by simp
      rw [← hy]
      change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M⁻¹
        (WithLp.toLp 2 y.ofLp)) = WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp)
      rw [Matrix.toEuclideanCLM_toLp]
    have hlow := hlower (WithLp.toLp 2 v)
    have hlow' : b * ‖WithLp.toLp 2 v‖ ≤ ‖WithLp.toLp 2 (M *ᵥ v)‖ := by
      change b * ‖WithLp.toLp 2 v‖ ≤
        ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M (WithLp.toLp 2 v))‖ at hlow
      rw [Matrix.toEuclideanCLM_toLp] at hlow
      exact hlow
    rw [hMv] at hlow'
    have hbound : b * ‖euclCLM (M⁻¹) y‖ ≤ ‖y‖ := by
      simpa [happly] using hlow'
    calc
      ‖euclCLM (M⁻¹) y‖ ≤ ‖y‖ / b := (le_div_iff₀ hb).2 (by simpa [mul_comm] using hbound)
      _ = b⁻¹ * ‖y‖ := by rw [div_eq_mul_inv]; ring
  have hnorm : ‖M⁻¹‖ = ‖euclCLM (M⁻¹)‖ := by
    change ‖M⁻¹‖ = ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun (M⁻¹)‖
    exact (Matrix.l2_opNorm_toEuclideanCLM (M⁻¹)).symm
  exact ⟨hunit, by simpa [hnorm] using hclm⟩
private lemma matrix_commute_nonsing_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Y : RMat ι) (hY : IsUnit Y) (hDY : D * Y = Y * D) :
    D * Y⁻¹ = Y⁻¹ * D := by
  have hdet : IsUnit Y.det := Y.isUnit_iff_isUnit_det.mp hY
  have hleft : Y⁻¹ * Y = 1 := by
    simpa using Matrix.nonsing_inv_mul_cancel_right (A := Y) (B := (1 : RMat ι)) hdet
  have hright : Y * Y⁻¹ = 1 := by
    simpa using Matrix.mul_nonsing_inv_cancel_right (A := Y) (B := (1 : RMat ι)) hdet
  calc
    D * Y⁻¹ = (Y⁻¹ * Y) * D * Y⁻¹ := by rw [hleft]; simp
    _ = Y⁻¹ * (Y * D) * Y⁻¹ := by noncomm_ring
    _ = Y⁻¹ * (D * Y) * Y⁻¹ := by rw [hDY]
    _ = Y⁻¹ * D * (Y * Y⁻¹) := by noncomm_ring
    _ = Y⁻¹ * D := by rw [hright]; simp

private lemma matrix_fill_conjugate {P T : Type*} [Fintype P] [DecidableEq P]
    [Fintype T] [DecidableEq T]
    (X : Matrix P T ℝ) (Y : RMat T) (Z : Matrix T P ℝ)
    (QA QAi : RMat P) (QT : RMat T)
    (hQA : QA * QAi = 1) (hX : QA * X = X * QT)
    (hY : QT * Y⁻¹ = Y⁻¹ * QT) (hZ : QT * Z = Z * QA) :
    QA * (X * Y⁻¹ * Z) * QAi = X * Y⁻¹ * Z := by
  calc
    QA * (X * Y⁻¹ * Z) * QAi = (QA * X) * Y⁻¹ * Z * QAi := by
      simp only [Matrix.mul_assoc]
    _ = (X * QT) * Y⁻¹ * Z * QAi := by rw [hX]
    _ = X * (QT * Y⁻¹) * Z * QAi := by simp only [Matrix.mul_assoc]
    _ = X * (Y⁻¹ * QT) * Z * QAi := by rw [hY]
    _ = X * Y⁻¹ * (QT * Z) * QAi := by simp only [Matrix.mul_assoc]
    _ = X * Y⁻¹ * (Z * QA) * QAi := by rw [hZ]
    _ = X * Y⁻¹ * Z * (QA * QAi) := by simp only [Matrix.mul_assoc]
    _ = X * Y⁻¹ * Z := by rw [hQA]; simp

private lemma matrix_entry_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMat ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j (1 : ℂ))
  have hxnorm : ‖x‖ = 1 := by
    simp [x]
  have hentry : (euclCLM A x).ofLp i = A i j := by
    change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
      (WithLp.toLp 2 (Pi.single j (1 : ℂ)))).ofLp i = A i j
    rw [Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec_single]
  have hcoordSq : ‖(euclCLM A x).ofLp i‖ ^ 2 ≤ ‖euclCLM A x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖(euclCLM A x).ofLp k‖)
      (Finset.mem_univ i)
  have hcoord : ‖(euclCLM A x).ofLp i‖ ≤ ‖euclCLM A x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hcoordSq
  have hclmnorm : ‖euclCLM A‖ = ‖A‖ := by
    change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun A‖ = ‖A‖
    exact (Matrix.l2_opNorm_toEuclideanCLM A).symm
  calc
    ‖A i j‖ = ‖(euclCLM A x).ofLp i‖ := by rw [hentry]
    _ ≤ ‖euclCLM A x‖ := hcoord
    _ ≤ ‖euclCLM A‖ * ‖x‖ := (euclCLM A).le_opNorm x
    _ = ‖A‖ := by rw [hxnorm, mul_one, hclmnorm]

private lemma matrix_l2_opNorm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ‖(1 : CMat ι)‖ ≤ 1 := by
  calc
    ‖(1 : CMat ι)‖ = ‖(diagonal (fun _ : ι => (1 : ℂ)) : CMat ι)‖ := by simp
    _ = ‖fun _ : ι => (1 : ℂ)‖ := Matrix.l2_opNorm_diagonal _
    _ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun _ => by simp)

private lemma real_abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  have hxnorm : ‖x‖ ≤ 1 := by simpa [Real.norm_eq_abs] using hx
  have htaylor := Real.norm_exp_sub_one_sub_id_le hxnorm
  have htriangle : ‖Real.exp x - 1‖ ≤ ‖Real.exp x - 1 - x‖ + ‖x‖ := by
    calc
      ‖Real.exp x - 1‖ = ‖(Real.exp x - 1 - x) + x‖ := by congr 1 <;> ring
      _ ≤ ‖Real.exp x - 1 - x‖ + ‖x‖ := norm_add_le _ _
  have habs : |Real.exp x - 1| ≤ |Real.exp x - 1 - x| + |x| := by
    simpa [Real.norm_eq_abs] using htriangle
  have hTaylorAbs : |Real.exp x - 1 - x| ≤ |x| ^ 2 := by
    simpa [Real.norm_eq_abs] using htaylor
  nlinarith [abs_nonneg x, hx]

private lemma terminalSchur_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : RMat ι) (A : Finset ι) (hH : H.IsSymm) :
    (terminalSchur H A).IsSymm := by
  classical
  let T := (↑(Aᶜ) : Type _)
  let X : Matrix A T ℝ := H.submatrix (fun i : A => i.val) (fun i : T => i.val)
  let Y : RMat T := restrict H Aᶜ
  let Z : Matrix T A ℝ := H.submatrix (fun i : T => i.val) (fun i : A => i.val)
  have hAA : (restrict H A).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [restrict, hH.apply]
  have hY : Y.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [Y, restrict, hH.apply]
  have hXZ : Z = X.transpose := by
    ext i j
    simp [X, Z, hH.apply]
  have hZX : Z.transpose = X := by
    simpa using congrArg Matrix.transpose hXZ
  have hYinv : (Y⁻¹).IsSymm := by
    change (Y⁻¹)ᵀ = Y⁻¹
    rw [Matrix.transpose_nonsing_inv, hY.eq]
  have hFill : (X * Y⁻¹ * Z).IsSymm := by
    change (X * Y⁻¹ * Z)ᵀ = X * Y⁻¹ * Z
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hZX, hYinv.eq, hXZ]
    simp [Matrix.mul_assoc]
  change (restrict H A - X * Y⁻¹ * Z).IsSymm
  change (restrict H A - X * Y⁻¹ * Z)ᵀ = restrict H A - X * Y⁻¹ * Z
  rw [Matrix.transpose_sub, hAA.eq, hFill.eq]

private lemma map_real_diagonal {P : Type*} [Fintype P] [DecidableEq P] (f : P → ℝ) :
    (diagonal f : RMat P).map (algebraMap ℝ ℂ) = diagonal (fun i => (f i : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h]

private lemma terminal_schur_fill_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (H : RMat ι) (A : Finset ι) (w winv : ι → ℝ)
    (hhop : ∀ i j, i ≠ j →
      (G.Adj i j → |H i j| ≤ 1) ∧ (¬ G.Adj i j → H i j = 0))
    (hweight : ∀ i j, G.Adj i j → (i ∈ Aᶜ ∨ j ∈ Aᶜ) → w i = w j)
    (hunit : IsUnit (restrict H Aᶜ)) (hwinv : ∀ i, w i * winv i = 1) :
    let X := H.submatrix (fun i : A => i.val) (fun i : (↑(Aᶜ) : Type _) => i.val)
    let Y := restrict H Aᶜ
    let Z := H.submatrix (fun i : (↑(Aᶜ) : Type _) => i.val) (fun i : A => i.val)
    (diagonal (fun i : A => w i.val)) * (X * Y⁻¹ * Z) *
        diagonal (fun i : A => winv i.val) = X * Y⁻¹ * Z := by
  classical
  let T := (↑(Aᶜ) : Type _)
  let X : Matrix A T ℝ := H.submatrix (fun i : A => i.val) (fun i : T => i.val)
  let Y : RMat T := restrict H Aᶜ
  let Z : Matrix T A ℝ := H.submatrix (fun i : T => i.val) (fun i : A => i.val)
  let QA : RMat A := diagonal (fun i => w i.val)
  let QAi : RMat A := diagonal (fun i => winv i.val)
  let QT : RMat T := diagonal (fun i => w i.val)
  have hQA : QA * QAi = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hwinv]
    · simp [hij]
  have hX : QA * X = X * QT := by
    ext i j
    simp only [QA, QT, X, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hadj : G.Adj i.val j.val
    · rw [hweight i.val j.val hadj (Or.inr j.property)]
      ring
    · have hne : i.val ≠ j.val := by
        intro heq
        have hjT : j.val ∉ A := Finset.mem_compl.mp j.property
        have hjT' : i.val ∉ A := by simpa [heq] using hjT
        exact hjT' i.property
      have hzero := (hhop i.val j.val hne).2 hadj
      simp [hzero]
  have hY : QT * Y = Y * QT := by
    ext i j
    simp only [QT, Y, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases heq : i.val = j.val
    · rw [heq]
      ring
    · by_cases hadj : G.Adj i.val j.val
      · rw [hweight i.val j.val hadj (Or.inl i.property)]
        ring
      · have hzero := (hhop i.val j.val heq).2 hadj
        simp [restrict, hzero]
  have hZ : QT * Z = Z * QA := by
    ext i j
    simp only [QT, QA, Z, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hadj : G.Adj i.val j.val
    · rw [hweight i.val j.val hadj (Or.inl i.property)]
      ring
    · have hne : i.val ≠ j.val := by
        intro heq
        have hiT : i.val ∉ A := Finset.mem_compl.mp i.property
        have hiT' : j.val ∉ A := by simpa [heq] using hiT
        exact hiT' j.property
      have hzero := (hhop i.val j.val hne).2 hadj
      simp [hzero]
  have hYinv : QT * Y⁻¹ = Y⁻¹ * QT :=
    matrix_commute_nonsing_inv QT Y (by simpa [Y, T] using hunit) hY
  change QA * (X * Y⁻¹ * Z) * QAi = X * Y⁻¹ * Z
  exact matrix_fill_conjugate X Y Z QA QAi QT hQA hX hYinv hZ

theorem locality_proof : ∀ (d : ℕ) (C : ℝ), 1 ≤ C → ∃ a > 0, ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (geo : FiniteGeometry (Fin n) d) (H : RMat (Fin n))
    (A : Finset (Fin n)) (τ : A → ℝ) (t : ℝ),
    0 < t → t < t0 → H.IsSymm →
    (∀ i j, i ≠ j → (geo.graph.Adj i j → |H i j| ≤ 1) ∧
      (¬ geo.graph.Adj i j → H i j = 0)) →
    IsUnit (restrict H Aᶜ) → (∀ i, t / C ≤ τ i ∧ τ i ≤ C * t) →
    IsUnit (dampedActive H A τ) ∧
    (∀ i j : A, ‖(Real.sqrt t : ℂ) * (dampedActive H A τ)⁻¹ i j‖ ≤
      C' / Real.sqrt t * Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j)) := by
  intro d C hC
  let a : ℝ := 1 / (16 * ((d : ℝ) + 1) * C)
  let Cout : ℝ := 2 * C
  let t0 : ℝ := 1
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have ha : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 := by
    dsimp [a]
    have hd1 : 1 ≤ (d : ℝ) + 1 := by
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
      linarith
    have hdplus : 0 ≤ (d : ℝ) + 1 := by linarith [hd1]
    have hdleft : 0 ≤ 16 * ((d : ℝ) + 1) := mul_nonneg (by norm_num) hdplus
    have hden : 1 ≤ 16 * ((d : ℝ) + 1) * C := by
      calc
        1 ≤ 16 := by norm_num
        _ ≤ 16 * ((d : ℝ) + 1) := by nlinarith [hd1]
        _ ≤ 16 * ((d : ℝ) + 1) * C := by
          calc
            16 * ((d : ℝ) + 1) = 16 * ((d : ℝ) + 1) * 1 := by ring
            _ ≤ 16 * ((d : ℝ) + 1) * C := mul_le_mul_of_nonneg_left hC hdleft
    rw [div_le_iff₀ (by positivity)]
    simpa using hden
  refine ⟨a, ha, Cout, by dsimp [Cout]; positivity, t0, by norm_num, ?_⟩
  intro n geo H A τ t ht ht0 hH hhop hterm hτ
  have hatle : a * t ≤ 1 := by
    calc
      a * t ≤ 1 * t := mul_le_mul_of_nonneg_right ha_le ht.le
      _ ≤ 1 := by linarith
  let S : RMat A := terminalSchur H A
  let Sc : CMat A := S.map (algebraMap ℝ ℂ)
  let M : CMat A := dampedActive H A τ
  have hSsymm : S.IsSymm := terminalSchur_isSymm H A hH
  have hScHerm : Sc.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Sc, hSsymm.apply]
  have hDam := damped_unit_inv_bound Sc hScHerm τ (t / C) (by positivity)
    (fun i => (hτ i).1)
  have hMunit : IsUnit M := by simpa [M, dampedActive, S, Sc] using hDam.1
  have hMInv : ‖M⁻¹‖ ≤ C / t := by
    calc
      ‖M⁻¹‖ ≤ (t / C)⁻¹ := by simpa [M, dampedActive, S, Sc] using hDam.2
      _ = C / t := by field_simp
  refine ⟨?_, ?_⟩
  · simpa [M] using hMunit
  · intro i j
    let z : A := j
    let q : Fin n → ℝ := fun k => Real.exp (a * t * collapsedDistance geo.graph Aᶜ k z.val)
    let qi : Fin n → ℝ := fun k => (q k)⁻¹
    have hqpos (k : Fin n) : 0 < q k := Real.exp_pos _
    have hqinv (k : Fin n) : q k * qi k = 1 := by simp [qi, q]
    have hqedge : ∀ k l, geo.graph.Adj k l →
        (k ∈ Aᶜ ∨ l ∈ Aᶜ) → q k = q l := by
      intro k l hkl hterminal
      have hd := collapsed_adj_eq_terminal geo.graph Aᶜ geo.connected
        (i := k) (j := l) (z := z.val) hkl hterminal
      simp [q, hd]
    let T := (↑(Aᶜ) : Type _)
    let Xblk : Matrix A T ℝ := H.submatrix (fun k : A => k.val) (fun k : T => k.val)
    let Yblk : RMat T := restrict H Aᶜ
    let Zblk : Matrix T A ℝ := H.submatrix (fun k : T => k.val) (fun k : A => k.val)
    let FillR : RMat A := Xblk * Yblk⁻¹ * Zblk
    let HAAc : CMat A := (restrict H A).map (algebraMap ℝ ℂ)
    let FillC : CMat A := FillR.map (algebraMap ℝ ℂ)
    let QAr : RMat A := diagonal (fun k => q k.val)
    let QAir : RMat A := diagonal (fun k => qi k.val)
    let QA : CMat A := diagonal (fun k => (q k.val : ℂ))
    let QAi : CMat A := diagonal (fun k => (qi k.val : ℂ))
    have hFillR : QAr * FillR * QAir = FillR := by
      simpa [QAr, QAir, FillR, Xblk, Yblk, Zblk] using
        terminal_schur_fill_conjugate geo.graph H A q qi hhop hqedge hterm hqinv
    have hQArMap : QAr.map (algebraMap ℝ ℂ) = QA := by
      simpa [QAr, QA] using map_real_diagonal (fun k : A => q k.val)
    have hQAirMap : QAir.map (algebraMap ℝ ℂ) = QAi := by
      simpa [QAir, QAi] using map_real_diagonal (fun k : A => qi k.val)
    have hFillC : QA * FillC * QAi = FillC := by
      have hmap := congrArg (fun B : RMat A => B.map (algebraMap ℝ ℂ)) hFillR
      simp only [Matrix.map_mul] at hmap
      rw [hQArMap, hQAirMap] at hmap
      simpa [FillC] using hmap
    have hMapFill : FillC = (Xblk * Yblk⁻¹ * Zblk).map (algebraMap ℝ ℂ) := rfl
    have hScEq : Sc = HAAc - FillC := by
      change (terminalSchur H A).map (algebraMap ℝ ℂ) =
        (restrict H A).map (algebraMap ℝ ℂ) - FillC
      have hreal : terminalSchur H A = restrict H A - FillR := by rfl
      rw [hreal]
      ext k l
      rw [hMapFill]
      simp only [Matrix.map_apply, Matrix.sub_apply]
      exact (algebraMap ℝ ℂ).map_sub _ _
    let Delta : CMat A := QA * HAAc * QAi - HAAc
    have hScConj : QA * Sc * QAi = Sc + Delta := by
      calc
        QA * Sc * QAi = QA * (HAAc - FillC) * QAi := by rw [hScEq]
        _ = QA * HAAc * QAi - QA * FillC * QAi := by noncomm_ring
        _ = QA * HAAc * QAi - FillC := by rw [hFillC]
        _ = (HAAc - FillC) + Delta := by dsimp [Delta]; abel
        _ = Sc + Delta := by rw [← hScEq]
    let Dτ : CMat A := diagonal (fun k => Complex.I * (τ k : ℂ))
    have hqcast (k : A) : (q k.val : ℂ) * (qi k.val : ℂ) = 1 := by
      exact_mod_cast hqinv k.val
    have hDconj : QA * Dτ * QAi = Dτ := by
      simp [QA, QAi, Dτ, Matrix.diagonal_mul_diagonal, hqcast,
        mul_assoc, mul_left_comm, mul_comm]
    have hMConj : QA * M * QAi = M + Delta := by
      change QA * (Sc - Dτ) * QAi = (Sc - Dτ) + Delta
      calc
        QA * (Sc - Dτ) * QAi = QA * Sc * QAi - QA * Dτ * QAi := by noncomm_ring
        _ = (Sc + Delta) - Dτ := by rw [hScConj, hDconj]
        _ = (Sc - Dτ) + Delta := by abel
    have hDeltaFormula (k l : A) :
        Delta k l = ((q k.val : ℂ) * (qi l.val : ℂ) - 1) * (H k.val l.val : ℂ) := by
      simp [Delta, QA, QAi, HAAc, restrict, Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    have hDeltaEntry (k l : A) : ‖Delta k l‖ ≤ 2 * a * t := by
      by_cases hkl : k = l
      · subst l
        have hqC : (q k.val : ℂ) * (qi k.val : ℂ) = 1 := by exact_mod_cast hqinv k.val
        rw [hDeltaFormula, hqC]
        simp
        positivity
      · have hval : k.val ≠ l.val := by
          intro heq
          exact hkl (Subtype.ext heq)
        by_cases hadj : geo.graph.Adj k.val l.val
        · have hkT : k.val ∉ Aᶜ := by simpa using k.property
          have hlT : l.val ∉ Aᶜ := by simpa using l.property
          have hdist := collapsed_adj_diff_le_one geo.graph Aᶜ geo.connected
            (i := k.val) (j := l.val) (z := z.val) hadj hkT hlT
          have hArgAbs : |a * t *
              (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)| ≤ a * t := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg ha.le ht.le)]
            calc
              a * t * |collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val| ≤ a * t * 1 :=
                  mul_le_mul_of_nonneg_left hdist (by positivity)
              _ = a * t := by ring
          have hArg : |a * t *
              (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)| ≤ 1 := hArgAbs.trans hatle
          have hExp := real_abs_exp_sub_one_le hArg
          have hratio : q k.val * qi l.val = Real.exp
              (a * t * (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)) := by
            dsimp [q, qi]
            rw [← div_eq_mul_inv, ← Real.exp_sub]
            congr 1
            ring
          have hfactor : (q k.val : ℂ) * (qi l.val : ℂ) - 1 =
              ((Real.exp (a * t * (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)) - 1 : ℝ) : ℂ) := by
            have h := congrArg (fun x : ℝ => (x : ℂ) - 1) hratio
            simpa using h
          have hhop := (hhop k.val l.val hval).1 hadj
          rw [hDeltaFormula k l, hfactor, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
          calc
            |Real.exp (a * t * (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)) - 1| * |H k.val l.val| ≤
                |Real.exp (a * t * (collapsedDistance geo.graph Aᶜ k.val z.val -
                  collapsedDistance geo.graph Aᶜ l.val z.val)) - 1| := by
                    simpa using mul_le_mul_of_nonneg_left hhop (abs_nonneg _)
            _ ≤ 2 * |a * t * (collapsedDistance geo.graph Aᶜ k.val z.val -
                collapsedDistance geo.graph Aᶜ l.val z.val)| := hExp
            _ ≤ 2 * (a * t) := mul_le_mul_of_nonneg_left hArgAbs (by positivity)
            _ = 2 * a * t := by ring
        · have hzero := (hhop k.val l.val hval).2 hadj
          rw [hDeltaFormula k l, hzero]
          simp
          positivity
    have hDeltaDiag : ∀ k : A, Delta k k = 0 := by
      intro k
      have hqC : (q k.val : ℂ) * (qi k.val : ℂ) = 1 := by exact_mod_cast hqinv k.val
      rw [hDeltaFormula, hqC]
      simp
    have hDeltaZero : ∀ k l : A, k ≠ l → ¬ geo.graph.Adj k.val l.val → Delta k l = 0 := by
      intro k l hkl hadj
      have hval : k.val ≠ l.val := by
        intro heq
        exact hkl (Subtype.ext heq)
      have hzero := (hhop k.val l.val hval).2 hadj
      rw [hDeltaFormula, hzero]
      simp
    have hSums := sparse_matrix_row_col_sum geo.graph (fun k : A => k.val)
      Subtype.val_injective d geo.degree Delta (2 * a * t) (by positivity)
      hDeltaEntry hDeltaDiag hDeltaZero
    let δ : ℝ := (2 * (d : ℝ)) * (2 * a * t)
    have hδ : 0 ≤ δ := by positivity
    have hDeltaOp : ‖Delta‖ ≤ 4 * (d : ℝ) * a * t := by
      have h := matrix_schur_opNorm_bound Delta δ δ hδ hδ
        (by simpa [δ] using hSums.1) (by simpa [δ] using hSums.2)
      calc
        ‖Delta‖ ≤ Real.sqrt (δ * δ) := h
        _ = δ := Real.sqrt_mul_self hδ
        _ = 4 * (d : ℝ) * a * t := by dsimp [δ]; ring
    let Xerr : CMat A := M⁻¹ * Delta
    have hXsmall : ‖Xerr‖ ≤ 1 / 2 := by
      calc
        ‖Xerr‖ ≤ ‖M⁻¹‖ * ‖Delta‖ := norm_mul_le _ _
        _ ≤ (C / t) * (4 * (d : ℝ) * a * t) :=
          mul_le_mul hMInv hDeltaOp (norm_nonneg _) (by positivity)
        _ = 4 * (d : ℝ) * C * a := by field_simp [ne_of_gt ht]
        _ ≤ 1 / 2 := by
          dsimp [a]
          have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
          field_simp
          nlinarith [mul_nonneg (show 0 ≤ 4 * (d : ℝ) + 8 by positivity) hCpos.le]
    let Tmat : CMat A := 1 + Xerr
    have hTlower : ∀ y : EuclideanSpace ℂ A,
        (1 / 2) * ‖y‖ ≤ ‖euclCLM Tmat y‖ := by
      intro y
      have hraw : (Tmat *ᵥ y.ofLp) - (Xerr *ᵥ y.ofLp) = y.ofLp := by
        simp [Tmat, Matrix.add_mulVec, Matrix.one_mulVec]
      have hidentity : euclCLM Tmat y - euclCLM Xerr y = y := by
        ext k
        change (Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ) Tmat y).ofLp k -
          (Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ) Xerr y).ofLp k = y.ofLp k
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
        exact congrArg (fun v : A → ℂ => v k) hraw
      have htriangle : ‖y‖ ≤ ‖euclCLM Tmat y‖ + ‖euclCLM Xerr y‖ := by
        calc
          ‖y‖ = ‖euclCLM Tmat y - euclCLM Xerr y‖ := by rw [hidentity]
          _ ≤ ‖euclCLM Tmat y‖ + ‖euclCLM Xerr y‖ := norm_sub_le _ _
      have hXclm : ‖euclCLM Xerr‖ ≤ 1 / 2 := by
        have hnorm : ‖euclCLM Xerr‖ = ‖Xerr‖ := by
          change ‖(Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ)).toFun Xerr‖ = ‖Xerr‖
          exact (Matrix.l2_opNorm_toEuclideanCLM Xerr).symm
        simpa [hnorm] using hXsmall
      have hXaction : ‖euclCLM Xerr y‖ ≤ (1 / 2) * ‖y‖ := by
        calc
          ‖euclCLM Xerr y‖ ≤ ‖euclCLM Xerr‖ * ‖y‖ := (euclCLM Xerr).le_opNorm y
          _ ≤ (1 / 2) * ‖y‖ := mul_le_mul_of_nonneg_right hXclm (norm_nonneg _)
      linarith
    have hTbounds := matrix_lower_inverse_bound Tmat (1 / 2) (by norm_num) hTlower
    have hMdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hMunit
    have hMMul : M * M⁻¹ = 1 := by
      simpa using Matrix.mul_nonsing_inv_cancel_right (A := M) (B := (1 : CMat A)) hMdet
    have hTdet : IsUnit Tmat.det := Tmat.isUnit_iff_isUnit_det.mp hTbounds.1
    have hTMul : Tmat * Tmat⁻¹ = 1 := by
      simpa using Matrix.mul_nonsing_inv_cancel_right (A := Tmat) (B := (1 : CMat A)) hTdet
    have hNfactor : QA * M * QAi = M * Tmat := by
      calc
        QA * M * QAi = M + Delta := hMConj
        _ = M * (1 + Xerr) := by
          dsimp [Tmat, Xerr]
          calc
            M + Delta = M + (M * M⁻¹) * Delta := by rw [hMMul]; simp
            _ = M * (1 + M⁻¹ * Delta) := by noncomm_ring
        _ = M * Tmat := by rfl
    have hNunit : IsUnit (QA * M * QAi) := by
      rw [hNfactor]
      exact hMunit.mul hTbounds.1
    let N : CMat A := QA * M * QAi
    let V : CMat A := Tmat⁻¹ * M⁻¹
    have hNmulV : N * V = 1 := by
      dsimp [N, V]
      rw [hNfactor]
      calc
        M * Tmat * (Tmat⁻¹ * M⁻¹) = M * (Tmat * Tmat⁻¹) * M⁻¹ := by noncomm_ring
        _ = M * 1 * M⁻¹ := by rw [hTMul]
        _ = 1 := by simp [hMMul]
    have hNdet : IsUnit N.det := N.isUnit_iff_isUnit_det.mp hNunit
    have hNinvLeft : N⁻¹ * N = 1 := by
      simpa using Matrix.nonsing_inv_mul_cancel_right (A := N) (B := (1 : CMat A)) hNdet
    have hNinvEq : N⁻¹ = V := by
      calc
        N⁻¹ = N⁻¹ * 1 := by simp
        _ = N⁻¹ * (N * V) := by rw [hNmulV]
        _ = (N⁻¹ * N) * V := by noncomm_ring
        _ = V := by simp [hNinvLeft]
    have hNinvNorm : ‖N⁻¹‖ ≤ 2 * (C / t) := by
      rw [hNinvEq]
      have hTinvNorm : ‖Tmat⁻¹‖ ≤ 2 := by norm_num at hTbounds; exact hTbounds.2
      calc
        ‖V‖ ≤ ‖Tmat⁻¹‖ * ‖M⁻¹‖ := norm_mul_le _ _
        _ ≤ 2 * (C / t) := mul_le_mul hTinvNorm hMInv (norm_nonneg _) (by positivity)
    have hQAprod : QA * QAi = 1 := by
      simp [QA, QAi, Matrix.diagonal_mul_diagonal, hqcast]
    have hQAiProd : QAi * QA = 1 := by
      simp [QAi, QA, Matrix.diagonal_mul_diagonal, hqcast, mul_comm]
    have hNinvConj : N⁻¹ = QA * M⁻¹ * QAi := by
      have hcand : N * (QA * M⁻¹ * QAi) = 1 := by
        dsimp [N]
        calc
          (QA * M * QAi) * (QA * M⁻¹ * QAi) = QA * M * (QAi * QA) * M⁻¹ * QAi := by noncomm_ring
          _ = QA * M * 1 * M⁻¹ * QAi := by rw [hQAiProd]
          _ = QA * (M * M⁻¹) * QAi := by noncomm_ring
          _ = QA * 1 * QAi := by rw [hMMul]
          _ = 1 := by simp [hQAprod]
      calc
        N⁻¹ = N⁻¹ * 1 := by simp
        _ = N⁻¹ * (N * (QA * M⁻¹ * QAi)) := by rw [hcand]
        _ = (N⁻¹ * N) * (QA * M⁻¹ * QAi) := by noncomm_ring
        _ = QA * M⁻¹ * QAi := by simp [hNinvLeft]
    have hNentryFormula (k l : A) :
        N⁻¹ k l = (q k.val : ℂ) * (M⁻¹ k l) * (qi l.val : ℂ) := by
      rw [hNinvConj]
      simp [QA, QAi, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_assoc]
    have hqz : q j.val = 1 := by
      simp [q, z, collapsed_self_eq_zero geo.graph Aᶜ geo.connected j.val]
    have hqiz : qi j.val = 1 := by simp [qi, hqz]
    have hNentryNorm : ‖N⁻¹ i j‖ = q i.val * ‖M⁻¹ i j‖ := by
      rw [hNentryFormula, hqiz]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (hqpos i.val)]
      simp
    have hMentry : ‖M⁻¹ i j‖ ≤ (2 * (C / t)) *
        Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j) := by
      have hprod : q i.val * ‖M⁻¹ i j‖ ≤ 2 * (C / t) := by
        rw [← hNentryNorm]
        exact (matrix_entry_le_opNorm N⁻¹ i j).trans hNinvNorm
      have hqpos' : 0 < q i.val := hqpos i.val
      calc
        ‖M⁻¹ i j‖ ≤ (2 * (C / t)) / q i.val := (le_div_iff₀ hqpos').2 (by simpa [mul_comm] using hprod)
        _ = (2 * (C / t)) * Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j) := by
          simp [q, z, Real.exp_neg, div_eq_mul_inv]
    have hfinal : ‖(Real.sqrt t : ℂ) * M⁻¹ i j‖ ≤
        Cout / Real.sqrt t * Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j) := by
      calc
        ‖(Real.sqrt t : ℂ) * M⁻¹ i j‖ = Real.sqrt t * ‖M⁻¹ i j‖ := by
          simp [Complex.norm_real, abs_of_pos (Real.sqrt_pos.2 ht)]
        _ ≤ Real.sqrt t * ((2 * (C / t)) * Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j)) :=
          mul_le_mul_of_nonneg_left hMentry (Real.sqrt_nonneg _)
        _ = Cout / Real.sqrt t * Real.exp (-a * t * collapsedDistance geo.graph Aᶜ i j) := by
          dsimp [Cout]
          have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
          field_simp [ne_of_gt ht, ne_of_gt hsqrt]
          rw [Real.sq_sqrt ht.le]
    exact hfinal

private lemma inverse_row_F_sums {ι : Type*} [Fintype ι] [DecidableEq ι] (t C β : ℝ)
    (s : State ι) (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hβ : 0 < β) (hclose : ∀ i, |s.q i - s.p i| ≤ C * power t β)
    (hpositive : ∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C)
    (hward : s.F t *ᵥ s.p = s.q) (hsymm : s.g.IsSymm) :
    (∀ i, ∑ j, s.F t i j ≤ 2 * C ^ 2) ∧
    (∀ j, ∑ i, s.F t i j ≤ 2 * C ^ 2) := by
  classical
  have hpow : power t β ≤ 1 := by
    dsimp [power]
    exact Real.rpow_le_one ht.le ht1 hβ.le
  have hq : ∀ i, s.q i ≤ 2 * C := by
    intro i
    have hi := hclose i
    have hi' : s.q i - s.p i ≤ C * power t β := (abs_le.mp hi).2
    have hp := (hpositive i).2
    nlinarith
  have hFp (i : ι) : ∑ j, s.F t i j * s.p j = s.q i := by
    have hi := congrFun hward i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hFnonneg (i j : ι) : 0 ≤ s.F t i j := by
    simp [State.F, entryAbsSquare]
  have hFsymm (i j : ι) : s.F t i j = s.F t j i := by
    simp [State.F, entryAbsSquare, State.h, hsymm.apply i j]
  have hrow (i : ι) : ∑ j, s.F t i j ≤ 2 * C ^ 2 := by
    have hterm (j : ι) : s.F t i j ≤ C * (s.F t i j * s.p j) := by
      have hp := (hpositive j).1
      have hmul : 1 ≤ C * s.p j := by
        have hmul' : 1 ≤ s.p j * C := (div_le_iff₀ (by linarith : 0 < C)).mp hp
        nlinarith
      nlinarith [hFnonneg i j]
    calc
      ∑ j, s.F t i j ≤ ∑ j, C * (s.F t i j * s.p j) := Finset.sum_le_sum fun j _ => hterm j
      _ = C * s.q i := by rw [← Finset.mul_sum, hFp i]
      _ ≤ 2 * C ^ 2 := by
        have hq' := hq i
        have hCnon : 0 ≤ C := by linarith
        calc
          C * s.q i ≤ C * (2 * C) := mul_le_mul_of_nonneg_left hq' hCnon
          _ = 2 * C ^ 2 := by ring
  constructor
  · exact hrow
  · intro j
    calc
      ∑ i, s.F t i j = ∑ i, s.F t j i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hFsymm]
      _ ≤ 2 * C ^ 2 := hrow j

private lemma inverse_row_power_mulVec_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (t C β : ℝ)
    (s : State ι) (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hβ : 0 < β) (hclose : ∀ i, |s.q i - s.p i| ≤ C * power t β)
    (hpositive : ∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C)
    (hward : s.F t *ᵥ s.p = s.q) (hsymm : s.g.IsSymm) :
    ∀ k i, ((s.F t) ^ k *ᵥ s.p) i ≤ (1 + C ^ 2 * power t β) ^ k * s.p i := by
  classical
  have hsums := inverse_row_F_sums t C β s hC ht ht1 hβ hclose hpositive hward hsymm
  have hpow : power t β ≤ 1 := by
    dsimp [power]
    exact Real.rpow_le_one ht.le ht1 hβ.le
  have hq : ∀ i, s.q i ≤ (1 + C ^ 2 * power t β) * s.p i := by
    intro i
    have hclose' := (abs_le.mp (hclose i)).2
    have hp := hpositive i
    have hpC : 1 ≤ C * s.p i := by
      have h := (div_le_iff₀ (by linarith : 0 < C)).mp hp.1
      nlinarith
    have hCnon : 0 ≤ C := by linarith
    have hβnon : 0 ≤ power t β := by
      dsimp [power]
      exact Real.rpow_nonneg ht.le β
    have herror : C * power t β ≤ C ^ 2 * power t β * s.p i := by
      calc
        C * power t β = 1 * (C * power t β) := by ring
        _ ≤ (C * s.p i) * (C * power t β) :=
          mul_le_mul_of_nonneg_right hpC (mul_nonneg hCnon hβnon)
        _ = C ^ 2 * power t β * s.p i := by ring
    nlinarith
  have hFp (i : ι) : ∑ j, s.F t i j * s.p j = s.q i := by
    have hi := congrFun hward i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hμpos : 0 < 1 + C ^ 2 * power t β := by
    have hβnon : 0 ≤ power t β := by
      dsimp [power]
      exact Real.rpow_nonneg ht.le β
    have hCnon : 0 ≤ C := by linarith
    nlinarith
  intro k
  induction k with
  | zero =>
      intro i
      simp
  | succ k ih =>
      intro i
      have hstep : (s.F t) ^ (k + 1) *ᵥ s.p =
          s.F t *ᵥ ((s.F t) ^ k *ᵥ s.p) := by
        rw [pow_succ', Matrix.mulVec_mulVec]
      rw [hstep]
      simp only [Matrix.mulVec_apply]
      calc
        (∑ j, s.F t i j * ((s.F t) ^ k *ᵥ s.p) j) ≤
            ∑ j, s.F t i j * ((1 + C ^ 2 * power t β) ^ k * s.p j) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (ih j) (by
              simp [State.F, entryAbsSquare])
        _ = (1 + C ^ 2 * power t β) ^ k *
              (∑ j, s.F t i j * s.p j) := by
          calc
            ∑ j, s.F t i j * ((1 + C ^ 2 * power t β) ^ k * s.p j) =
                ∑ j, (1 + C ^ 2 * power t β) ^ k * (s.F t i j * s.p j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = (1 + C ^ 2 * power t β) ^ k *
                (∑ j, s.F t i j * s.p j) := by rw [Finset.mul_sum]
        _ = (1 + C ^ 2 * power t β) ^ k * s.q i := by rw [hFp i]
        _ ≤ (1 + C ^ 2 * power t β) ^ k *
              ((1 + C ^ 2 * power t β) * s.p i) :=
          mul_le_mul_of_nonneg_left (hq i) (pow_nonneg hμpos.le k)
        _ = (1 + C ^ 2 * power t β) ^ (k + 1) * s.p i := by rw [pow_succ]; ring

private lemma inverse_row_Fpow_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (s : State ι)
    (hF : ∀ i j, 0 ≤ s.F t i j) :
    ∀ (k : ℕ) (i j : ι), 0 ≤ ((s.F t) ^ k) i j := by
  classical
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j <;> simp [hij]
  | succ k ih =>
      intro i j
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hF l j)

private lemma inverse_row_power_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (s : State ι) :
    (∀ i j, ‖s.K t i j‖ = s.F t i j) →
    (∀ i j, 0 ≤ s.F t i j) →
    ∀ (k : ℕ) (i j : ι), ‖((s.K t) ^ k) i j‖ ≤ ((s.F t) ^ k) i j := by
  classical
  intro hK hF
  have hFpow := inverse_row_Fpow_nonneg t s hF
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | succ k ih =>
      intro i j
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      calc
        ‖∑ l, ((s.K t) ^ k) i l * s.K t l j‖ ≤
            ∑ l, ‖((s.K t) ^ k) i l * s.K t l j‖ := norm_sum_le _ _
        _ ≤ ∑ l, ((s.F t) ^ k) i l * s.F t l j :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul]
            exact mul_le_mul (ih i l) (le_of_eq (hK l j)) (norm_nonneg _) (hFpow k i l)
        _ = ((s.F t) ^ (k + 1)) i j := by
          rw [pow_succ]
          simp [Matrix.mul_apply]

private lemma inverse_row_power_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (t C β : ℝ)
    (s : State ι) (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hβ : 0 < β) (hclose : ∀ i, |s.q i - s.p i| ≤ C * power t β)
    (hpositive : ∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C)
    (hward : s.F t *ᵥ s.p = s.q) (hsymm : s.g.IsSymm) :
    ∀ (k : ℕ) (i : ι), ∑ j, ‖((s.K t) ^ k) i j‖ ≤
      C ^ 2 * (1 + C ^ 2 * power t β) ^ k := by
  classical
  have hFnonneg (i j : ι) : 0 ≤ s.F t i j := by
    simp [State.F, entryAbsSquare]
  have hKnorm (i j : ι) : ‖s.K t i j‖ = s.F t i j := by
    change ‖(s.h t i j) ^ 2‖ = ‖s.h t i j‖ ^ 2
    exact norm_pow _ _
  have hpowEntry := inverse_row_power_entry_bound t s hKnorm hFnonneg
  have hpowNonneg := inverse_row_Fpow_nonneg t s hFnonneg
  have hvec := inverse_row_power_mulVec_bound t C β s hC ht ht1 hβ hclose hpositive hward hsymm
  have hμnon : 0 ≤ 1 + C ^ 2 * power t β := by
    have hp : 0 ≤ power t β := by
      dsimp [power]
      exact Real.rpow_nonneg ht.le β
    nlinarith [show 0 ≤ C by linarith]
  have hCnon : 0 ≤ C := by linarith
  intro k i
  calc
    ∑ j, ‖((s.K t) ^ k) i j‖ ≤ ∑ j, ((s.F t) ^ k) i j :=
      Finset.sum_le_sum fun j _ => hpowEntry k i j
    _ ≤ C * ((s.F t) ^ k *ᵥ s.p) i := by
      have hterm (j : ι) : ((s.F t) ^ k) i j ≤
          C * (((s.F t) ^ k) i j * s.p j) := by
        have hp := (hpositive j).1
        have hmul : 1 ≤ C * s.p j := by
          have hh := (div_le_iff₀ (by linarith : 0 < C)).mp hp
          nlinarith
        nlinarith [hpowNonneg k i j]
      calc
        ∑ j, ((s.F t) ^ k) i j ≤
            ∑ j, C * (((s.F t) ^ k) i j * s.p j) :=
          Finset.sum_le_sum fun j _ => hterm j
        _ = C * ((s.F t) ^ k *ᵥ s.p) i := by
          rw [← Finset.mul_sum]
          simp [Matrix.mulVec, dotProduct]
    _ ≤ C * ((1 + C ^ 2 * power t β) ^ k * s.p i) :=
      mul_le_mul_of_nonneg_left (hvec k i) hCnon
    _ ≤ C ^ 2 * (1 + C ^ 2 * power t β) ^ k := by
      have hpi := (hpositive i).2
      calc
        C * ((1 + C ^ 2 * power t β) ^ k * s.p i) ≤
            C * ((1 + C ^ 2 * power t β) ^ k * C) := by
          apply mul_le_mul_of_nonneg_left _ hCnon
          exact mul_le_mul_of_nonneg_left hpi (pow_nonneg hμnon k)
        _ = C ^ 2 * (1 + C ^ 2 * power t β) ^ k := by ring

private lemma shell_distance_center_diff {P : Type*} [Fintype P]
    (d : ℕ) (C : ℝ) (dist : P → P → ℝ) (hshell : ShellBounds d C dist)
    (z i j : P) : |dist z i - dist z j| ≤ dist i j := by
  have h₁ := hshell.triangle z j i
  have h₂ := hshell.triangle z i j
  rw [hshell.symmetric j i] at h₁
  rw [abs_le]
  constructor <;> linarith

private lemma shell_exp_count {P : Type*} [Fintype P]
    (d : ℕ) (C : ℝ) (dist : P → P → ℝ) (hshell : ShellBounds d C dist)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (i : P) :
    ∑ j, Real.exp (-u * dist i j) ≤ C * power u (-(d : ℝ)) :=
  hshell.count u hu hu1 i

private lemma real_abs_exp_sub_one_le_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| := by
  by_cases hx : 0 ≤ x
  · have hE : 1 ≤ Real.exp x := by
      simpa using (Real.exp_le_exp.mpr hx)
    rw [abs_of_nonneg (sub_nonneg.mpr hE), abs_of_nonneg hx]
    linarith [Real.exp_pos x]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hE : Real.exp x ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr hx')
    rw [abs_of_nonpos (sub_nonpos.mpr hE)]
    have heq : -(Real.exp x - 1) = 1 - Real.exp x := by ring
    rw [heq]
    calc
      1 - Real.exp x ≤ 1 := by linarith [Real.exp_pos x]
      _ ≤ Real.exp |x| := by
        have h := Real.exp_le_exp.mpr (abs_nonneg x)
        simpa using h

private lemma power_neg_two_inv_sq (t : ℝ) : power t (-2) = t⁻¹ ^ 2 := by
  dsimp [power]
  rw [Real.rpow_neg_eq_inv_rpow]
  exact Real.rpow_natCast _ _

private lemma t_cube_mul_power_neg_two (t : ℝ) (ht : 0 < t) :
    t ^ 3 * power t (-2) = t := by
  rw [power_neg_two_inv_sq]
  field_simp

private def inverseRowTilt {ι : Type*} (K : CMat ι) (u : ℝ)
    (dist : ι → ι → ℝ) (z : ι) : CMat ι :=
  fun i j => (Real.exp (u * (dist z i - dist z j)) : ℂ) * K i j

private lemma inverseRowTilt_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMat ι) (u : ℝ) (dist : ι → ι → ℝ) (z : ι) :
    inverseRowTilt A u dist z * inverseRowTilt B u dist z =
      inverseRowTilt (A * B) u dist z := by
  classical
  ext i j
  simp only [Matrix.mul_apply, inverseRowTilt]
  calc
    ∑ k, (Real.exp (u * (dist z i - dist z k)) : ℂ) * A i k *
        ((Real.exp (u * (dist z k - dist z j)) : ℂ) * B k j) =
      ∑ k, (Real.exp (u * (dist z i - dist z j)) : ℂ) * (A i k * B k j) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hreal : Real.exp (u * (dist z i - dist z k)) *
            Real.exp (u * (dist z k - dist z j)) =
            Real.exp (u * (dist z i - dist z j)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hfactor : (Real.exp (u * (dist z i - dist z k)) : ℂ) *
            (Real.exp (u * (dist z k - dist z j)) : ℂ) =
            (Real.exp (u * (dist z i - dist z j)) : ℂ) := by exact_mod_cast hreal
        calc
          (Real.exp (u * (dist z i - dist z k)) : ℂ) * A i k *
              ((Real.exp (u * (dist z k - dist z j)) : ℂ) * B k j) =
            ((Real.exp (u * (dist z i - dist z k)) : ℂ) *
              (Real.exp (u * (dist z k - dist z j)) : ℂ)) * (A i k * B k j) := by ring
          _ = (Real.exp (u * (dist z i - dist z j)) : ℂ) * (A i k * B k j) := by
            rw [hfactor]
    _ = (Real.exp (u * (dist z i - dist z j)) : ℂ) *
          ∑ k, A i k * B k j := by rw [Finset.mul_sum]
    _ = (inverseRowTilt (A * B) u dist z) i j := by
      simp [inverseRowTilt, Matrix.mul_apply]

private lemma inverseRowTilt_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : CMat ι) (u : ℝ) (dist : ι → ι → ℝ) (z : ι) (k : ℕ) :
    (inverseRowTilt K u dist z) ^ k = inverseRowTilt (K ^ k) u dist z := by
  induction k with
  | zero =>
      ext i j
      by_cases hij : i = j
      · subst j
        simp [inverseRowTilt]
      · simp [inverseRowTilt, hij]
  | succ k ih =>
      rw [pow_succ, ih, inverseRowTilt_mul, pow_succ]

private lemma inverse_row_power_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : CMat ι) (u α : ℝ) (dist : ι → ι → ℝ)
    (hself : ∀ i, dist i i = 0) (hsymm : ∀ i j, dist i j = dist j i)
    (hTnorm : ∀ z, ‖inverseRowTilt K u dist z‖ ≤ α) :
    ∀ k i j, ‖(K ^ k) i j‖ ≤ α ^ k * Real.exp (-u * dist i j) := by
  classical
  intro k i j
  let T := inverseRowTilt K u dist j
  have hpow : inverseRowTilt (K ^ k) u dist j = T ^ k := by
    symm
    exact inverseRowTilt_pow K u dist j k
  have hα : 0 ≤ α := le_trans (norm_nonneg T) (hTnorm j)
  have hTpow : ∀ m, ‖T ^ m‖ ≤ α ^ m := by
    intro m
    induction m with
    | zero => simpa using matrix_l2_opNorm_one_le (ι := ι)
    | succ m ih =>
        rw [pow_succ]
        calc
          ‖T ^ m * T‖ ≤ ‖T ^ m‖ * ‖T‖ := norm_mul_le _ _
          _ ≤ α ^ m * α := mul_le_mul (ih) (hTnorm j) (norm_nonneg _) (pow_nonneg hα m)
          _ = α ^ (m + 1) := by rw [pow_succ]
  have hentry : ‖(inverseRowTilt (K ^ k) u dist j) i j‖ ≤ α ^ k := by
    calc
      ‖(inverseRowTilt (K ^ k) u dist j) i j‖ ≤
          ‖inverseRowTilt (K ^ k) u dist j‖ := matrix_entry_le_opNorm _ _ _
      _ = ‖T ^ k‖ := by rw [hpow]
      _ ≤ α ^ k := hTpow k
  have hentry0 :
      ‖(Real.exp (u * (dist j i - dist j j)) : ℂ) * (K ^ k) i j‖ ≤ α ^ k := by
    simpa [inverseRowTilt] using hentry
  have hentry1 : ‖(Real.exp (u * (dist j i - dist j j)) : ℂ)‖ *
      ‖(K ^ k) i j‖ ≤ α ^ k := by rwa [norm_mul] at hentry0
  have hRealNorm : ‖(Real.exp (u * (dist j i - dist j j)) : ℂ)‖ =
      Real.exp (u * (dist j i - dist j j)) := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.exp_nonneg _)
  have hfactor : Real.exp (u * (dist j i - dist j j)) = Real.exp (u * dist i j) := by
    rw [hself j, hsymm j i]
    ring_nf
  have hentry2 : Real.exp (u * (dist i j)) * ‖(K ^ k) i j‖ ≤ α ^ k := by
    rw [hRealNorm, hfactor] at hentry1
    exact hentry1
  have hexp : 0 < Real.exp (u * dist i j) := Real.exp_pos _
  calc
    ‖(K ^ k) i j‖ ≤ α ^ k / Real.exp (u * dist i j) :=
      (le_div_iff₀ hexp).2 (by simpa [mul_comm] using hentry2)
    _ = α ^ k * Real.exp (-u * dist i j) := by
      rw [div_eq_mul_inv]
      congr 1
      rw [show -u * dist i j = -(u * dist i j) by ring, Real.exp_neg]

private lemma inverse_row_tilt_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : CMat ι) (u : ℝ) (dist : ι → ι → ℝ) (z : ι)
    (q : ι → ℝ) (hq : ∀ i, q i = Real.exp (u * dist z i)) :
    diagonal (fun i => (q i : ℂ)) * K *
      diagonal (fun i => ((q i)⁻¹ : ℂ)) = inverseRowTilt K u dist z := by
  classical
  have hr (i j : ι) : q i * (q j)⁻¹ =
      Real.exp (u * (dist z i - dist z j)) := by
    rw [hq i, hq j]
    rw [← div_eq_mul_inv, ← Real.exp_sub]
    congr 1
    ring
  have hqC (i j : ι) : (q i : ℂ) * ((q j)⁻¹ : ℂ) =
      (Real.exp (u * (dist z i - dist z j)) : ℂ) := by
    exact_mod_cast hr i j
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, inverseRowTilt]
  have harg : (u : ℂ) * ((dist z i : ℂ) - (dist z j : ℂ)) =
      ((u * (dist z i - dist z j) : ℝ) : ℂ) := by
    push_cast
    ring
  have hce : Complex.exp ((u : ℂ) * ((dist z i : ℂ) - (dist z j : ℂ))) =
      (Real.exp (u * (dist z i - dist z j)) : ℂ) := by
    rw [harg, ← Complex.ofReal_exp]
  rw [hce, ← hqC i j]
  ring

private lemma inverse_row_tilt_inverse_entry_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (K : CMat ι) (u α : ℝ)
    (dist : ι → ι → ℝ) (hself : ∀ i, dist i i = 0)
    (hsymm : ∀ i j, dist i j = dist j i)
    (hTnorm : ∀ z, ‖inverseRowTilt K u dist z‖ ≤ α)
    (hMunit : IsUnit (1 - K)) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∀ i j, ‖(1 - K)⁻¹ i j‖ ≤ (1 - α)⁻¹ * Real.exp (-u * dist i j) := by
  classical
  intro i j
  let q : ι → ℝ := fun k => Real.exp (u * dist j k)
  let qi : ι → ℝ := fun k => (q k)⁻¹
  let D : CMat ι := diagonal (fun k => (q k : ℂ))
  let Di : CMat ι := diagonal (fun k => (qi k : ℂ))
  let T : CMat ι := inverseRowTilt K u dist j
  let M : CMat ι := 1 - K
  let N : CMat ι := 1 - T
  have hqpos (k : ι) : 0 < q k := Real.exp_pos _
  have hqinv (k : ι) : q k * qi k = 1 := by
    dsimp [qi]
    exact mul_inv_cancel₀ (ne_of_gt (hqpos k))
  have hqiinv (k : ι) : qi k * q k = 1 := by
    dsimp [qi]
    exact inv_mul_cancel₀ (ne_of_gt (hqpos k))
  have hqcast (k : ι) : (q k : ℂ) * (qi k : ℂ) = 1 := by exact_mod_cast hqinv k
  have hqicast (k : ι) : (qi k : ℂ) * (q k : ℂ) = 1 := by exact_mod_cast hqiinv k
  have hDprod : D * Di = 1 := by
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [D, Di, Matrix.diagonal_mul_diagonal, hqcast]
    · simp [D, Di, hkl]
  have hDiD : Di * D = 1 := by
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [D, Di, Matrix.diagonal_mul_diagonal, hqicast]
    · simp [D, Di, hkl]
  have hTilt : D * K * Di = T := by
    simpa [D, Di, T, q, qi] using
      inverse_row_tilt_diagonal K u dist j q (fun _ => rfl)
  have hNconj : N = D * M * Di := by
    dsimp [N, M]
    calc
      1 - T = D * Di - T := by rw [← hDprod]
      _ = D * Di - D * K * Di := by rw [hTilt]
      _ = D * 1 * Di - D * K * Di := by simp
      _ = D * (1 - K) * Di := by noncomm_ring
  have hNlower : ∀ y : EuclideanSpace ℂ ι,
      (1 - α) * ‖y‖ ≤ ‖euclCLM N y‖ := by
    intro y
    have hraw : (1 - T) *ᵥ y.ofLp + T *ᵥ y.ofLp = y.ofLp := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    have hidentity : euclCLM N y + euclCLM T y = y := by
      ext k
      change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) N y).ofLp k +
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) T y).ofLp k = y.ofLp k
      rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
      exact congrArg (fun v : ι → ℂ => v k) hraw
    have htri : ‖y‖ ≤ ‖euclCLM N y‖ + ‖euclCLM T y‖ := by
      calc
        ‖y‖ = ‖euclCLM N y + euclCLM T y‖ := by rw [hidentity]
        _ ≤ ‖euclCLM N y‖ + ‖euclCLM T y‖ := norm_add_le _ _
    have hTclm : ‖euclCLM T‖ ≤ α := by
      have hnorm : ‖euclCLM T‖ = ‖T‖ := by
        change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toFun T‖ = ‖T‖
        exact (Matrix.l2_opNorm_toEuclideanCLM T).symm
      rw [hnorm]
      exact hTnorm j
    have hTaction : ‖euclCLM T y‖ ≤ α * ‖y‖ := by
      calc
        ‖euclCLM T y‖ ≤ ‖euclCLM T‖ * ‖y‖ := (euclCLM T).le_opNorm y
        _ ≤ α * ‖y‖ := mul_le_mul_of_nonneg_right hTclm (norm_nonneg _)
    nlinarith
  have hNbounds := matrix_lower_inverse_bound N (1 - α)
    (sub_pos.mpr hα1) hNlower
  have hMdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hMunit
  have hMP : M * M⁻¹ = 1 := by
    simpa [M] using Matrix.mul_nonsing_inv_cancel_right (A := M) (B := (1 : CMat ι)) hMdet
  have hNdet : IsUnit N.det := N.isUnit_iff_isUnit_det.mp hNbounds.1
  have hNinvLeft : N⁻¹ * N = 1 := by
    simpa using Matrix.nonsing_inv_mul_cancel_right (A := N) (B := (1 : CMat ι)) hNdet
  have hNCand : N * (D * M⁻¹ * Di) = 1 := by
    rw [hNconj]
    calc
      (D * M * Di) * (D * M⁻¹ * Di) = D * M * (Di * D) * M⁻¹ * Di := by noncomm_ring
      _ = D * M * 1 * M⁻¹ * Di := by rw [hDiD]
      _ = D * (M * M⁻¹) * Di := by noncomm_ring
      _ = D * 1 * Di := by rw [hMP]
      _ = D * Di := by simp
      _ = 1 := hDprod
  have hNinv : N⁻¹ = D * M⁻¹ * Di := by
    calc
      N⁻¹ = N⁻¹ * 1 := by simp
      _ = N⁻¹ * (N * (D * M⁻¹ * Di)) := by rw [hNCand]
      _ = (N⁻¹ * N) * (D * M⁻¹ * Di) := by noncomm_ring
      _ = D * M⁻¹ * Di := by rw [hNinvLeft]; simp
  have hformula (k l : ι) :
      N⁻¹ k l = (q k : ℂ) * (M⁻¹ k l) * (qi l : ℂ) := by
    rw [hNinv]
    simp [D, Di, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_assoc]
  have hqj : q j = 1 := by simp [q, hself j]
  have hqij : qi j = 1 := by simp [qi, hqj]
  have hqi : q i = Real.exp (u * dist i j) := by
    simp [q, hsymm j i]
  have hformulaNorm : ‖N⁻¹ i j‖ = Real.exp (u * dist i j) * ‖M⁻¹ i j‖ := by
    have hqnorm : ‖(q i : ℂ)‖ = Real.exp (u * dist i j) := by
      rw [Complex.norm_real, Real.norm_eq_abs, hqi]
      exact abs_of_pos (Real.exp_pos _)
    have hqijnorm : ‖(qi j : ℂ)‖ = 1 := by rw [hqij]; simp
    calc
      ‖N⁻¹ i j‖ = ‖(q i : ℂ) * (M⁻¹ i j) * (qi j : ℂ)‖ := by rw [hformula]
      _ = ‖(q i : ℂ)‖ * ‖M⁻¹ i j‖ * ‖(qi j : ℂ)‖ := by simp [norm_mul]
      _ = Real.exp (u * dist i j) * ‖M⁻¹ i j‖ := by rw [hqnorm, hqijnorm]; ring
  have hentry : ‖N⁻¹ i j‖ ≤ (1 - α)⁻¹ :=
    (matrix_entry_le_opNorm N⁻¹ i j).trans hNbounds.2
  rw [hformulaNorm] at hentry
  have hexp : 0 < Real.exp (u * dist i j) := Real.exp_pos _
  calc
    ‖M⁻¹ i j‖ ≤ (1 - α)⁻¹ / Real.exp (u * dist i j) :=
      (le_div_iff₀ hexp).2 (by simpa [mul_comm] using hentry)
    _ = (1 - α)⁻¹ * Real.exp (-u * dist i j) := by
      rw [div_eq_mul_inv]
      congr 1
      rw [show -u * dist i j = -(u * dist i j) by ring, Real.exp_neg]

private lemma inverse_row_tilt_delta_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (C t : ℝ)
    (s : State ι) (dist : ι → ι → ℝ)
    (hshell : ShellBounds d C dist) (hC : 1 ≤ C) (ht : 0 < t)
    (htsmall : t ≤ 1 / C)
    (hfar : ∀ i j, C * power t (-2) < dist i j →
      ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C))
    (z i j : ι) :
    ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ ≤
      2 * C * t * s.F t i j +
        (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
          Real.exp (-t * dist i j / (2 * C)) := by
  have hCpos : 0 < C := by linarith
  have hCnon : 0 ≤ C := hCpos.le
  have htle1 : t ≤ 1 := by
    have hle : 1 / C ≤ 1 := by
      rw [div_le_iff₀ hCpos]
      linarith
    exact le_trans htsmall hle
  have hCt : C * t ≤ 1 := by
    calc
      C * t ≤ C * (1 / C) := mul_le_mul_of_nonneg_left htsmall hCnon
      _ = 1 := by field_simp
  have ht2 : t ^ 2 ≤ 1 / C := by
    have hprod : 0 ≤ t * (1 - t) := mul_nonneg ht.le (sub_nonneg.mpr htle1)
    nlinarith
  have ht3 : t ^ 3 ≤ t / C := by
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ ≤ t * (1 / C) := mul_le_mul_of_nonneg_left ht2 ht.le
      _ = t / C := by ring
  have hFnonneg (x y : ι) : 0 ≤ s.F t x y := by
    simp [State.F, entryAbsSquare]
  have hKnorm (x y : ι) : ‖s.K t x y‖ = s.F t x y := by
    change ‖(s.h t x y) ^ 2‖ = ‖s.h t x y‖ ^ 2
    exact norm_pow _ _
  have hdiff := shell_distance_center_diff d C dist hshell z i j
  have hdist : 0 ≤ dist i j := hshell.nonneg i j
  have habs : |t ^ 3 * (dist z i - dist z j)| ≤ t ^ 3 * dist i j := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  have harg : (t ^ 3 : ℂ) * ((dist z i : ℂ) - (dist z j : ℂ)) =
      ((t ^ 3 * (dist z i - dist z j) : ℝ) : ℂ) := by
    push_cast
    ring
  have hce : Complex.exp ((t ^ 3 : ℂ) * ((dist z i : ℂ) - (dist z j : ℂ))) =
      (Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) := by
    rw [harg, ← Complex.ofReal_exp]
  have hnormFormula :
      ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ =
        |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| * s.F t i j := by
    calc
      ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ =
          ‖Complex.exp ((t ^ 3 : ℂ) * ((dist z i : ℂ) - (dist z j : ℂ))) *
            s.K t i j - s.K t i j‖ := by rw [inverseRowTilt, hce]
      _ = ‖(Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) * s.K t i j -
          s.K t i j‖ := by rw [hce]
      _ =
          ‖((Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) - 1) * s.K t i j‖ := by
        congr 1
        ring
      _ = ‖(Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) - 1‖ *
            ‖s.K t i j‖ := norm_mul _ _
      _ = |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| * s.F t i j := by
        have hreal :
            ‖(Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) - 1‖ =
              |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| := by
          have hcast : (Real.exp (t ^ 3 * (dist z i - dist z j)) : ℂ) - 1 =
              ((Real.exp (t ^ 3 * (dist z i - dist z j)) - 1 : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hcast]
          simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [hreal, hKnorm]
  by_cases hnear : dist i j ≤ C * power t (-2)
  · have hnearDist : t ^ 3 * dist i j ≤ C * t := by
      calc
        t ^ 3 * dist i j ≤ t ^ 3 * (C * power t (-2)) :=
          mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = C * t := by
          calc
            t ^ 3 * (C * power t (-2)) = C * (t ^ 3 * power t (-2)) := by ring
            _ = C * t := by rw [t_cube_mul_power_neg_two t ht]
    have hx : |t ^ 3 * (dist z i - dist z j)| ≤ 1 :=
      (habs.trans hnearDist).trans hCt
    have hsmallExp := real_abs_exp_sub_one_le hx
    rw [hnormFormula]
    calc
      |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| * s.F t i j ≤
          (2 * |t ^ 3 * (dist z i - dist z j)|) * s.F t i j :=
        mul_le_mul_of_nonneg_right hsmallExp (hFnonneg i j)
      _ ≤ (2 * (C * t)) * s.F t i j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (habs.trans hnearDist) (by norm_num))
          (hFnonneg i j)
      _ ≤ 2 * C * t * s.F t i j +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            Real.exp (-t * dist i j / (2 * C)) := by
        have hfarNon : 0 ≤ (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            Real.exp (-t * dist i j / (2 * C)) := by positivity
        nlinarith [hfarNon]
  · have hfar' : C * power t (-2) < dist i j := lt_of_not_ge hnear
    have hpowDiv : power t (-2) = 1 / t ^ 2 := by
      rw [power_neg_two_inv_sq]
      field_simp
    have hfarDist : C / t ^ 2 < dist i j := by
      calc
        C / t ^ 2 = C * power t (-2) := by rw [hpowDiv]; ring
        _ < dist i j := hfar'
    have hfarThreshold : 1 / (2 * t) < t * dist i j / (2 * C) := by
      have hmul := mul_lt_mul_of_pos_right hfarDist (by positivity : 0 < t / (2 * C))
      field_simp [ne_of_gt ht, ne_of_gt hCpos] at hmul ⊢
      nlinarith
    have hcomp : t ^ 3 * dist i j - 2 * t * dist i j / C ≤
        -1 / (2 * t) - t * dist i j / (2 * C) := by
      have hA : t ^ 3 * dist i j ≤ t * dist i j / C := by
        calc
          t ^ 3 * dist i j ≤ (t / C) * dist i j :=
            mul_le_mul_of_nonneg_right ht3 hdist
          _ = t * dist i j / C := by ring
      have hX : 1 / t < t * dist i j / C := by
        have hmul := mul_lt_mul_of_pos_right hfarDist (by positivity : 0 < t / C)
        calc
          1 / t = (C / t ^ 2) * (t / C) := by
            field_simp [ne_of_gt ht, ne_of_gt hCpos]
          _ < dist i j * (t / C) := hmul
          _ = t * dist i j / C := by ring
      have hhalf : t * dist i j / (2 * C) = (t * dist i j / C) / 2 := by
        field_simp [ne_of_gt hCpos]
      have hXhalf : 1 / (2 * t) < (t * dist i j / C) / 2 := by
        calc
          1 / (2 * t) = (1 / t) * (1 / 2) := by field_simp [ne_of_gt ht]
          _ < (t * dist i j / C) * (1 / 2) :=
            mul_lt_mul_of_pos_right hX (by norm_num)
          _ = (t * dist i j / C) / 2 := by ring
      calc
        t ^ 3 * dist i j - 2 * t * dist i j / C ≤
            t * dist i j / C - 2 * t * dist i j / C :=
          sub_le_sub_right hA (2 * t * dist i j / C)
        _ = -t * dist i j / C := by ring
        _ = -(t * dist i j / C) := by ring
        _ ≤ -1 / (2 * t) - t * dist i j / (2 * C) := by
          rw [hhalf]
          calc
            -(t * dist i j / C) =
                -(t * dist i j / C) / 2 - (t * dist i j / C) / 2 := by ring
            _ = (-(t * dist i j / C) / 2) + (-(t * dist i j / C) / 2) := by ring
            _ ≤ (-(1 / (2 * t))) + (-(t * dist i j / C) / 2) := by
              nlinarith [sub_le_sub_right (neg_le_neg hXhalf.le) (t * dist i j / C / 2)]
            _ = -1 / (2 * t) - (t * dist i j / C) / 2 := by ring
    have hxexp : |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| ≤
        Real.exp (t ^ 3 * dist i j) := by
      calc
        |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| ≤
            Real.exp |t ^ 3 * (dist z i - dist z j)| :=
          real_abs_exp_sub_one_le_exp_abs _
        _ ≤ Real.exp (t ^ 3 * dist i j) := Real.exp_le_exp.mpr habs
    have hFfar : s.F t i j ≤
        (C / Real.sqrt t * Real.exp (-t * dist i j / C)) ^ 2 := by
      simpa [State.F, entryAbsSquare] using
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hfar i j hfar')
    have hsquare :
        (C / Real.sqrt t * Real.exp (-t * dist i j / C)) ^ 2 =
          (C / Real.sqrt t) ^ 2 * Real.exp (-2 * t * dist i j / C) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [hnormFormula]
    calc
      |Real.exp (t ^ 3 * (dist z i - dist z j)) - 1| * s.F t i j ≤
          Real.exp (t ^ 3 * dist i j) *
            (C / Real.sqrt t * Real.exp (-t * dist i j / C)) ^ 2 :=
        mul_le_mul hxexp hFfar (hFnonneg i j) (Real.exp_nonneg _)
      _ = (C / Real.sqrt t) ^ 2 *
            Real.exp (t ^ 3 * dist i j - 2 * t * dist i j / C) := by
        rw [hsquare]
        calc
          Real.exp (t ^ 3 * dist i j) *
              ((C / Real.sqrt t) ^ 2 * Real.exp (-2 * t * dist i j / C)) =
              (C / Real.sqrt t) ^ 2 *
                (Real.exp (t ^ 3 * dist i j) * Real.exp (-2 * t * dist i j / C)) := by ring
          _ = (C / Real.sqrt t) ^ 2 *
                Real.exp (t ^ 3 * dist i j + (-2 * t * dist i j / C)) := by
            rw [← Real.exp_add]
          _ = (C / Real.sqrt t) ^ 2 *
                Real.exp (t ^ 3 * dist i j - 2 * t * dist i j / C) := by congr 2 <;> ring
      _ ≤ (C / Real.sqrt t) ^ 2 *
            Real.exp (-1 / (2 * t) - t * dist i j / (2 * C)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomp) (sq_nonneg _)
      _ = (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            Real.exp (-t * dist i j / (2 * C)) := by
        rw [show -1 / (2 * t) - t * dist i j / (2 * C) =
          -1 / (2 * t) + (-t * dist i j / (2 * C)) by ring, Real.exp_add]
        ring
      _ ≤ 2 * C * t * s.F t i j +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            Real.exp (-t * dist i j / (2 * C)) := by
        have hnon : 0 ≤ 2 * C * t * s.F t i j :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnon) ht.le) (hFnonneg i j)
        linarith

private lemma inverse_row_tilt_delta_sums {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (C t β : ℝ)
    (s : State ι) (dist : ι → ι → ℝ)
    (hshell : ShellBounds d C dist) (hC : 1 ≤ C) (ht : 0 < t)
    (ht1 : t ≤ 1) (htsmall : t ≤ 1 / C) (hβ : 0 < β)
    (hclose : ∀ i, |s.q i - s.p i| ≤ C * power t β)
    (hpositive : ∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C)
    (hward : s.F t *ᵥ s.p = s.q) (hsymm : s.g.IsSymm)
    (hfar : ∀ i j, C * power t (-2) < dist i j →
      ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C))
    (z : ι) :
    (∀ i, ∑ j, ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ ≤
      4 * C ^ 3 * t + (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
        (C * power (t / (2 * C)) (-(d : ℝ)))) ∧
    (∀ j, ∑ i, ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ ≤
      4 * C ^ 3 * t + (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
        (C * power (t / (2 * C)) (-(d : ℝ)))) := by
  classical
  have hCpos : 0 < C := by linarith
  have hFsums := inverse_row_F_sums t C β s hC ht ht1 hβ hclose hpositive hward hsymm
  have hu : 0 < t / (2 * C) := by positivity
  have hu1 : t / (2 * C) ≤ 1 := by
    have hInvLe : 1 / C ≤ 1 := (div_le_iff₀ hCpos).2 (by linarith)
    have htle : t ≤ 1 := le_trans htsmall hInvLe
    rw [div_le_iff₀ (by positivity : 0 < 2 * C)]
    nlinarith [hC, htle]
  have hE : 0 ≤ (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) := by positivity
  have hpow : 0 ≤ power (t / (2 * C)) (-(d : ℝ)) := by
    dsimp [power]
    exact Real.rpow_nonneg hu.le _
  have hnearCoeff : 0 ≤ 2 * C * t := by positivity
  have hfarCoeff : 0 ≤ (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) := hE
  have hcount (i : ι) :
      ∑ j, Real.exp (-(t / (2 * C)) * dist i j) ≤
        C * power (t / (2 * C)) (-(d : ℝ)) := by
    exact shell_exp_count d C dist hshell (t / (2 * C)) hu hu1 i
  have hcountRow (i : ι) :
      ∑ j, Real.exp (-t * dist i j / (2 * C)) ≤
        C * power (t / (2 * C)) (-(d : ℝ)) := by
    calc
      ∑ j, Real.exp (-t * dist i j / (2 * C)) =
          ∑ j, Real.exp (-(t / (2 * C)) * dist i j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      _ ≤ C * power (t / (2 * C)) (-(d : ℝ)) := hcount i
  constructor
  · intro i
    have hterm (j : ι) := inverse_row_tilt_delta_entry_bound C t s dist
      hshell hC ht htsmall hfar z i j
    calc
      ∑ j, ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ ≤
          ∑ j, (2 * C * t * s.F t i j +
            (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
              Real.exp (-t * dist i j / (2 * C))) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * C * t * (∑ j, s.F t i j) +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (∑ j, Real.exp (-t * dist i j / (2 * C))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * C * t * (2 * C ^ 2) +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (C * power (t / (2 * C)) (-(d : ℝ))) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hFsums.1 i) hnearCoeff)
          (mul_le_mul_of_nonneg_left (hcountRow i) hfarCoeff)
      _ = 4 * C ^ 3 * t +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (C * power (t / (2 * C)) (-(d : ℝ))) := by ring
  · intro j
    have hterm (i : ι) := inverse_row_tilt_delta_entry_bound C t s dist
      hshell hC ht htsmall hfar z i j
    have hcountCol :
        ∑ i, Real.exp (-(t / (2 * C)) * dist i j) ≤
          C * power (t / (2 * C)) (-(d : ℝ)) := by
      calc
        ∑ i, Real.exp (-(t / (2 * C)) * dist i j) =
            ∑ i, Real.exp (-(t / (2 * C)) * dist j i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hshell.symmetric i j]
        _ ≤ C * power (t / (2 * C)) (-(d : ℝ)) := hcount j
    have hcountCol' :
        ∑ i, Real.exp (-t * dist i j / (2 * C)) ≤
          C * power (t / (2 * C)) (-(d : ℝ)) := by
      calc
        ∑ i, Real.exp (-t * dist i j / (2 * C)) =
            ∑ i, Real.exp (-(t / (2 * C)) * dist i j) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          ring
        _ ≤ C * power (t / (2 * C)) (-(d : ℝ)) := hcountCol
    calc
      ∑ i, ‖inverseRowTilt (s.K t) (t ^ 3) dist z i j - s.K t i j‖ ≤
          ∑ i, (2 * C * t * s.F t i j +
            (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
              Real.exp (-t * dist i j / (2 * C))) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * C * t * (∑ i, s.F t i j) +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (∑ i, Real.exp (-t * dist i j / (2 * C))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * C * t * (2 * C ^ 2) +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (C * power (t / (2 * C)) (-(d : ℝ))) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hFsums.2 j) hnearCoeff)
          (mul_le_mul_of_nonneg_left hcountCol' hfarCoeff)
      _ = 4 * C ^ 3 * t +
          (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
            (C * power (t / (2 * C)) (-(d : ℝ))) := by ring
private lemma inverse_row_exp_lower_power (x : ℝ) (N : ℕ) (hN : 0 < N)
    (hx : 0 ≤ x) : (x / (N : ℝ)) ^ N ≤ Real.exp x := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hy : 0 ≤ x / (N : ℝ) := div_nonneg hx (by positivity)
  have hsum : x / (N : ℝ) ≤ 1 + x / (N : ℝ) := by linarith
  calc
    (x / (N : ℝ)) ^ N ≤ (1 + x / (N : ℝ)) ^ N :=
      pow_le_pow_left₀ hy hsum N
    _ ≤ Real.exp (x / (N : ℝ)) ^ N := by
      have hh := pow_le_pow_left₀ (by positivity)
        (Real.add_one_le_exp (x / (N : ℝ))) N
      simpa [add_comm] using hh
    _ = Real.exp x := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [ne_of_gt hNr]

private lemma inverse_row_one_div_rpow_div {x N : ℝ} (hx : 0 < x) (hN : 0 < N)
    (k : ℕ) : 1 / ((x / N) ^ k) = (N / x) ^ k := by
  rw [div_pow, div_pow]
  field_simp [ne_of_gt hx, ne_of_gt hN] <;> ring

private lemma inverse_row_cancel_power_div {x N : ℝ} (hx : 0 < x) (k : ℕ) :
    x ^ k * (N / x) ^ (k + 2) = N ^ (k + 2) / x ^ 2 := by
  simp only [div_pow, pow_add]
  field_simp [ne_of_gt hx] <;> ring

private lemma inverse_row_far_profile_small (d : ℕ) (C ε : ℝ)
    (hC : 0 < C) (hε : 0 < ε) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
        (C * power (t / (2 * C)) (-(d : ℝ))) ≤ ε := by
  let N : ℕ := d + 3
  let Nr : ℝ := (N : ℝ)
  let B : ℝ := 2 * C ^ 3 * (4 * C) ^ d
  let A : ℝ := B * Nr ^ N
  let X : ℝ := A / ε + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hNr : 0 < Nr := by dsimp [Nr]; exact_mod_cast hN
  have hB : 0 < B := by positivity
  have hA : 0 < A := by positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hXone : 1 ≤ X := by
    dsimp [X]
    have hAdiv : 0 ≤ A / ε := by positivity
    linarith
  refine ⟨1 / (2 * X), by positivity, ?_⟩
  intro t ht ht0
  let x : ℝ := 1 / (2 * t)
  have hmul : t * (2 * X) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * X)).mp ht0
  have hx : X < x := by
    dsimp [x]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * t)]
    nlinarith
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxone : 1 ≤ x := le_trans hXone hx.le
  have hExpLower := inverse_row_exp_lower_power x N hN hxpos.le
  have hpowBase : 0 < (x / Nr) ^ N := by positivity
  have hExpNeg : Real.exp (-x) ≤ (Nr / x) ^ N := by
    calc
      Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg]; simp
      _ ≤ 1 / ((x / Nr) ^ N) := one_div_le_one_div_of_le hpowBase hExpLower
      _ = (Nr / x) ^ N := inverse_row_one_div_rpow_div hxpos hNr N
  have hNsplit : N = (d + 1) + 2 := by dsimp [N]
  have hcore : x ^ (d + 1) * Real.exp (-x) ≤ Nr ^ N / x ^ 2 := by
    calc
      x ^ (d + 1) * Real.exp (-x) ≤ x ^ (d + 1) * (Nr / x) ^ N :=
        mul_le_mul_of_nonneg_left hExpNeg (pow_nonneg hxpos.le _)
      _ = Nr ^ N / x ^ 2 := by
        rw [hNsplit]
        exact inverse_row_cancel_power_div hxpos (d + 1)
  have hprofile (ht : 0 < t) :
      (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
          (C * power (t / (2 * C)) (-(d : ℝ))) =
        B * (x ^ (d + 1) * Real.exp (-x)) := by
    have hroot : (C / Real.sqrt t) ^ 2 = 2 * C ^ 2 * x := by
      dsimp [x]
      rw [div_pow, Real.sq_sqrt ht.le]
      field_simp [ne_of_gt ht]
    have hinv : (t / (2 * C))⁻¹ = 4 * C * x := by
      dsimp [x]
      field_simp [ne_of_gt ht, ne_of_gt hC]
      ring
    have hpow : power (t / (2 * C)) (-(d : ℝ)) = (4 * C * x) ^ d := by
      dsimp [power]
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, hinv]
    have hmulPow : (4 * C * x) ^ d = (4 * C) ^ d * x ^ d := by rw [mul_pow]
    rw [hroot, hpow, hmulPow]
    have hexp : -1 / (2 * t) = -x := by dsimp [x]; ring
    rw [hexp]
    change 2 * C ^ 2 * x * Real.exp (-x) * (C * ((4 * C) ^ d * x ^ d)) =
      B * (x ^ (d + 1) * Real.exp (-x))
    dsimp [B, N, Nr, A, X]
    rw [pow_succ]
    ring
  have hAover : A / ε < x := by
    dsimp [X] at hx
    linarith
  have hsmallA : A / x ≤ ε := by
    apply (div_le_iff₀ hxpos).2
    nlinarith [((div_lt_iff₀ hε).mp hAover).le]
  have hxx : x ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hinv : 1 / x ^ 2 ≤ 1 / x := one_div_le_one_div_of_le hxpos hxx
  have hpowDiv : Nr ^ N / x ^ 2 ≤ Nr ^ N / x := by
    calc
      Nr ^ N / x ^ 2 = Nr ^ N * (1 / x ^ 2) := by ring
      _ ≤ Nr ^ N * (1 / x) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = Nr ^ N / x := by ring
  calc
    (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
        (C * power (t / (2 * C)) (-(d : ℝ))) =
        B * (x ^ (d + 1) * Real.exp (-x)) := hprofile ht
    _ ≤ B * (Nr ^ N / x ^ 2) := mul_le_mul_of_nonneg_left hcore hB.le
    _ ≤ A / x := by
      calc
        B * (Nr ^ N / x ^ 2) ≤ B * (Nr ^ N / x) :=
          mul_le_mul_of_nonneg_left hpowDiv hB.le
        _ = A / x := by dsimp [A]; ring
    _ ≤ ε := hsmallA

private lemma inverse_row_log_power_bound {t β : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hβ : 0 < β) :
    logFactor t * power t β ≤ 1 + 1 / β := by
  have hpow : power t β ≤ 1 := by
    dsimp [power]
    exact Real.rpow_le_one ht.le ht1 hβ.le
  have hlog : 0 ≤ Real.log (1 / t) :=
    Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hlog_bound : Real.log (1 / t) ≤ (1 / t) ^ β / β :=
    Real.log_le_rpow_div (by positivity) hβ
  have hinv : (1 / t) ^ β * power t β = 1 := by
    dsimp [power]
    rw [one_div, Real.inv_rpow ht.le, inv_mul_cancel₀
      (ne_of_gt (Real.rpow_pos_of_pos ht β))]
  unfold logFactor
  calc
    (1 + Real.log (1 / t)) * power t β ≤
        (1 + (1 / t) ^ β / β) * power t β :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht.le β)
    _ = power t β + ((1 / t) ^ β * power t β) / β := by ring
    _ = power t β + 1 / β := by rw [hinv]
    _ ≤ 1 + 1 / β := by linarith

private lemma inverse_row_cutoff_power {d : ℕ} {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    α ^ Nat.ceil ((6 * (d : ℝ) / (-Real.log α)) * Real.log (1 / t)) ≤
      t ^ (6 * d) := by
  let ell : ℝ := -Real.log α
  let L : ℝ := Real.log (1 / t)
  let A : ℝ := 6 * (d : ℝ) / ell
  let N : ℕ := Nat.ceil (A * L)
  have hell : 0 < ell := by
    dsimp [ell]
    exact neg_pos.mpr (Real.log_neg hα hα1)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hN : A * L ≤ (N : ℝ) := by
    dsimp [N]
    exact Nat.le_ceil _
  have hlogInv : Real.log (1 / t) = -Real.log t := by
    rw [one_div, Real.log_inv]
  have harg : (N : ℝ) * Real.log α ≤ (6 * (d : ℝ)) * Real.log t := by
    have hscale : 6 * (d : ℝ) * L ≤ (N : ℝ) * ell := by
      calc
        6 * (d : ℝ) * L = (A * L) * ell := by
          dsimp [A]
          field_simp [ne_of_gt hell]
        _ ≤ (N : ℝ) * ell := mul_le_mul_of_nonneg_right hN hell.le
    dsimp [L, ell] at hscale
    rw [hlogInv] at hscale
    nlinarith
  have hαpow : α ^ N = Real.exp ((N : ℝ) * Real.log α) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hα]
    congr 1
    ring
  have htarg : Real.exp ((6 * (d : ℝ)) * Real.log t) = t ^ (6 * d) := by
    symm
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos ht]
    congr 1
    push_cast
    ring
  calc
    α ^ N = Real.exp ((N : ℝ) * Real.log α) := hαpow
    _ ≤ Real.exp ((6 * (d : ℝ)) * Real.log t) := Real.exp_le_exp.mpr harg
    _ = t ^ (6 * d) := htarg

private lemma inverse_row_cube_shell_cancel {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ (6 * d) * power (t ^ 3) (-(d : ℝ)) ^ 2 = 1 := by
  have hpow : ((t ^ 3) ^ d) ^ 2 = t ^ (6 * d) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hu : 0 < t ^ 3 := by positivity
  have hrpow : power (t ^ 3) (-(d : ℝ)) = ((t ^ 3) ^ d)⁻¹ := by
    dsimp [power]
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]
  rw [hrpow, inv_pow, hpow]
  have htPow : 0 < t ^ (6 * d) := by positivity
  exact mul_inv_cancel₀ (ne_of_gt htPow)

private lemma inverse_row_contraction_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : CMat ι) (α : ℝ) (hK : ‖K‖ ≤ α) (hα : α < 1) :
    IsUnit (1 - K) ∧ ‖(1 - K)⁻¹‖ ≤ (1 - α)⁻¹ := by
  apply matrix_lower_inverse_bound (1 - K) (1 - α) (sub_pos.mpr hα)
  intro y
  have hidentity : euclCLM (1 - K) y + euclCLM K y = y := by
    ext i
    change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (1 - K) y).ofLp i +
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) K y).ofLp i = y.ofLp i
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  have htri : ‖y‖ ≤ ‖euclCLM (1 - K) y‖ + ‖euclCLM K y‖ := by
    calc
      ‖y‖ = ‖euclCLM (1 - K) y + euclCLM K y‖ := by rw [hidentity]
      _ ≤ _ := norm_add_le _ _
  have hnorm : ‖euclCLM K‖ = ‖K‖ := (Matrix.l2_opNorm_toEuclideanCLM K).symm
  have haction : ‖euclCLM K y‖ ≤ α * ‖y‖ := by
    calc
      ‖euclCLM K y‖ ≤ ‖euclCLM K‖ * ‖y‖ := (euclCLM K).le_opNorm y
      _ ≤ α * ‖y‖ := mul_le_mul_of_nonneg_right (by simpa [hnorm] using hK)
        (norm_nonneg _)
  nlinarith

private lemma inverse_row_geometric_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : CMat ι) (hunit : IsUnit (1 - K)) (N : ℕ) :
    (1 - K)⁻¹ = (∑ k ∈ Finset.range N, K ^ k) + K ^ N * (1 - K)⁻¹ := by
  have hmul : (1 - K) * (1 - K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((1 - K).isUnit_iff_isUnit_det.mp hunit)
  have hbase : (1 - K)⁻¹ = 1 + K * (1 - K)⁻¹ := by
    rw [sub_mul, one_mul] at hmul
    exact sub_eq_iff_eq_add.mp hmul
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      (1 - K)⁻¹ = (∑ k ∈ Finset.range N, K ^ k) + K ^ N * (1 - K)⁻¹ := ih
      _ = (∑ k ∈ Finset.range N, K ^ k) + K ^ N * (1 + K * (1 - K)⁻¹) := by
        conv_rhs => rw [← hbase]
      _ = (∑ k ∈ Finset.range (N + 1), K ^ k) + K ^ (N + 1) * (1 - K)⁻¹ := by
        rw [Finset.sum_range_succ, pow_succ]
        noncomm_ring

private lemma inverse_row_short_power_uniform {t β A C : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hβ : 0 < β) (hA : 0 ≤ A)
    (k : ℕ) (hk : (k : ℝ) ≤ (A + 1) * logFactor t) :
    (1 + C ^ 2 * power t β) ^ k ≤
      Real.exp (C ^ 2 * (A + 1) * (1 + 1 / β)) := by
  have hp : 0 ≤ power t β := Real.rpow_nonneg ht.le _
  have hlog := inverse_row_log_power_bound ht ht1 hβ
  have harg : (k : ℝ) * (C ^ 2 * power t β) ≤
      C ^ 2 * (A + 1) * (1 + 1 / β) := by
    calc
      (k : ℝ) * (C ^ 2 * power t β) ≤
          ((A + 1) * logFactor t) * (C ^ 2 * power t β) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = C ^ 2 * (A + 1) * (logFactor t * power t β) := by ring
      _ ≤ C ^ 2 * (A + 1) * (1 + 1 / β) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    (1 + C ^ 2 * power t β) ^ k ≤ Real.exp (C ^ 2 * power t β) ^ k :=
      pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using
        (Real.add_one_le_exp (C ^ 2 * power t β))) k
    _ = Real.exp ((k : ℝ) * (C ^ 2 * power t β)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr harg

private lemma inverse_row_decay_tail_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (K P : CMat ι)
    (dist : ι → ι → ℝ) (C u α B : ℝ) (N : ℕ)
    (hα : 0 ≤ α) (hB : 0 ≤ B) (hu : 0 < u) (hu1 : u ≤ 1)
    (hshell : ShellBounds d C dist)
    (hpow : ∀ i j, ‖(K ^ N) i j‖ ≤ α ^ N * Real.exp (-u * dist i j))
    (hP : ∀ i j, ‖P i j‖ ≤ B * Real.exp (-u * dist i j)) :
    ∀ i, ∑ j, ‖(K ^ N * P) i j‖ ≤
      α ^ N * B * (C * power u (-(d : ℝ))) ^ 2 := by
  classical
  intro i
  have hentry (j : ι) : ‖(K ^ N * P) i j‖ ≤
      ∑ l, (α ^ N * Real.exp (-u * dist i l)) *
        (B * Real.exp (-u * dist l j)) := by
    rw [Matrix.mul_apply]
    calc
      ‖∑ l, (K ^ N) i l * P l j‖ ≤ ∑ l, ‖(K ^ N) i l * P l j‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (hpow i l) (hP l j) (norm_nonneg _) (by positivity)
  calc
    ∑ j, ‖(K ^ N * P) i j‖ ≤
        ∑ j, ∑ l, (α ^ N * Real.exp (-u * dist i l)) *
          (B * Real.exp (-u * dist l j)) := Finset.sum_le_sum fun j _ => hentry j
    _ = ∑ l, (α ^ N * Real.exp (-u * dist i l)) *
        (B * ∑ j, Real.exp (-u * dist l j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ l, (α ^ N * Real.exp (-u * dist i l)) *
        (B * (C * power u (-(d : ℝ)))) := by
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hshell.count u hu hu1 l) hB
    _ = α ^ N * B * (C * power u (-(d : ℝ))) *
        (∑ l, Real.exp (-u * dist i l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ α ^ N * B * (C * power u (-(d : ℝ))) *
        (C * power u (-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left (hshell.count u hu hu1 i)
      have hC : 0 ≤ C * power u (-(d : ℝ)) :=
        (Finset.sum_nonneg fun l _ => Real.exp_nonneg _).trans (hshell.count u hu hu1 i)
      positivity
    _ = α ^ N * B * (C * power u (-(d : ℝ))) ^ 2 := by ring


set_option maxHeartbeats 1600000 in
private theorem inverse_row_finite : ∀ (d : ℕ) (C ρ β : ℝ), 1 ≤ C → 0 ≤ ρ → ρ < 1 → 0 < β →
    ∃ C' > 0, ∃ c > 0, ∃ t0 > 0, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ)
    (s : State ι) (dist : ι → ι → ℝ),
    0 < t → t < t0 → ShellBounds d C dist → ‖s.K t‖ ≤ ρ → s.g.IsSymm →
    (∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C) → s.F t *ᵥ s.p = s.q →
    (∀ i, |s.q i - s.p i| ≤ C * power t β) →
    (∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t) →
    (∀ i j, C * power t (-2) < dist i j →
      ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C)) →
    IsUnit (1 - s.K t) ∧ rowNorm (s.P t) ≤ C' * logFactor t ∧
    (∀ i j, ‖s.P t i j‖ ≤ C' * Real.exp (-c * t^3 * dist i j)) := by
  classical
  intro d C ρ β hC hρ0 hρ1 hβ
  let ε : ℝ := (1 - ρ) / 4
  let α : ℝ := (1 + ρ) / 2
  let B : ℝ := (1 - α)⁻¹
  let A : ℝ := 6 * (d : ℝ) / (-Real.log α)
  let E : ℝ := Real.exp (C ^ 2 * (A + 1) * (1 + 1 / β))
  let Cout : ℝ := C ^ 2 * E * (A + 1) + B * C ^ 2 + B
  have hCpos : 0 < C := by linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) (neg_pos.mpr (Real.log_neg hα hα1)).le
  have hE : 0 < E := Real.exp_pos _
  have hCout : 0 < Cout := by dsimp [Cout]; positivity
  obtain ⟨tf, htf, hfarSmall⟩ := inverse_row_far_profile_small d C ε hCpos hε
  let t0 : ℝ := min 1 (min (1 / C) (min (ε / (4 * C ^ 3)) tf))
  have ht0 : 0 < t0 := by dsimp [t0]; positivity
  refine ⟨Cout, hCout, 1, by norm_num, t0, ht0, ?_⟩
  intro ι _ _ t s dist ht htt0 hshell hK hsymm hp hFp hclose _hcrude hfar
  have ht1 : t ≤ 1 := (lt_of_lt_of_le htt0 (min_le_left _ _)).le
  have htC : t ≤ 1 / C := by
    exact (lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_left _ _))).le
  have htε : t ≤ ε / (4 * C ^ 3) := by
    exact (lt_of_lt_of_le htt0 ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))).le
  have httf : t < tf := lt_of_lt_of_le htt0 ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hnear : 4 * C ^ 3 * t ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C ^ 3)).mp htε
    nlinarith
  have hfarSmallt := hfarSmall t ht httf
  have hTnorm : ∀ z, ‖inverseRowTilt (s.K t) (t ^ 3) dist z‖ ≤ α := by
    intro z
    let R : ℝ := 4 * C ^ 3 * t + (C / Real.sqrt t) ^ 2 * Real.exp (-1 / (2 * t)) *
      (C * power (t / (2 * C)) (-(d : ℝ)))
    have hR : 0 ≤ R := by dsimp [R, power]; positivity
    have hsums := inverse_row_tilt_delta_sums C t β s dist hshell hC ht ht1 htC
      hβ hclose hp hFp hsymm hfar z
    have hdelta : ‖inverseRowTilt (s.K t) (t ^ 3) dist z - s.K t‖ ≤ R := by
      calc
        ‖inverseRowTilt (s.K t) (t ^ 3) dist z - s.K t‖ ≤ Real.sqrt (R * R) :=
          matrix_schur_opNorm_bound _ R R hR hR hsums.1 hsums.2
        _ = R := Real.sqrt_mul_self hR
    calc
      ‖inverseRowTilt (s.K t) (t ^ 3) dist z‖ ≤ ‖s.K t‖ +
          ‖inverseRowTilt (s.K t) (t ^ 3) dist z - s.K t‖ := norm_le_insert' _ _
      _ ≤ ρ + R := add_le_add hK hdelta
      _ ≤ α := by
        dsimp [R, α]
        have hεEq : ρ + 2 * ε = (1 + ρ) / 2 := by dsimp [ε]; ring
        linarith only [hnear, hfarSmallt, hεEq]
  have hunit : IsUnit (1 - s.K t) := (inverse_row_contraction_inverse _ ρ hK hρ1).1
  have hPdecay := inverse_row_tilt_inverse_entry_bound (s.K t) (t ^ 3) α dist
    hshell.self hshell.symmetric hTnorm hunit hα.le hα1
  have hpowdecay := inverse_row_power_decay (s.K t) (t ^ 3) α dist
    hshell.self hshell.symmetric hTnorm
  let N : ℕ := Nat.ceil (A * Real.log (1 / t))
  have hlog : 0 ≤ Real.log (1 / t) :=
    Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hlogF : 1 ≤ logFactor t := by dsimp [logFactor]; linarith
  have hN : (N : ℝ) ≤ (A + 1) * logFactor t := by
    have hn := (Nat.ceil_lt_add_one (mul_nonneg hA hlog)).le
    change (⌈A * Real.log (1 / t)⌉₊ : ℝ) ≤ (A + 1) * logFactor t
    dsimp [logFactor]
    nlinarith
  have hshort : ∀ k ∈ Finset.range N, ∀ i, ∑ j, ‖((s.K t) ^ k) i j‖ ≤ C ^ 2 * E := by
    intro k hk i
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_range.mp hk).le
    calc
      ∑ j, ‖((s.K t) ^ k) i j‖ ≤ C ^ 2 * (1 + C ^ 2 * power t β) ^ k :=
        inverse_row_power_row_sum_bound t C β s hC ht ht1 hβ hclose hp hFp hsymm k i
      _ ≤ C ^ 2 * E := mul_le_mul_of_nonneg_left
        (inverse_row_short_power_uniform ht ht1 hβ hA k (hkN.trans hN)) (sq_nonneg C)
  have hu : 0 < t ^ 3 := by positivity
  have hu1 : t ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ ht.le ht1 3
  have htail : ∀ i, ∑ j, ‖((s.K t) ^ N * s.P t) i j‖ ≤ B * C ^ 2 := by
    intro i
    have htCut : α ^ N ≤ t ^ (6 * d) := inverse_row_cutoff_power hα hα1 ht ht1
    have hcancel := inverse_row_cube_shell_cancel (d := d) ht
    calc
      ∑ j, ‖((s.K t) ^ N * s.P t) i j‖ ≤
          α ^ N * B * (C * power (t ^ 3) (-(d : ℝ))) ^ 2 :=
        inverse_row_decay_tail_sum (s.K t) (s.P t) dist C (t ^ 3) α B N hα.le hB.le hu hu1
          hshell (hpowdecay N) hPdecay i
      _ ≤ t ^ (6 * d) * B * (C * power (t ^ 3) (-(d : ℝ))) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htCut hB.le) (sq_nonneg _)
      _ = B * C ^ 2 := by
        calc
          t ^ (6 * d) * B * (C * power (t ^ 3) (-(d : ℝ))) ^ 2 =
              (B * C ^ 2) * (t ^ (6 * d) * power (t ^ 3) (-(d : ℝ)) ^ 2) := by ring
          _ = B * C ^ 2 := by rw [hcancel, mul_one]
  have hrow : ∀ i, ∑ j, ‖s.P t i j‖ ≤ Cout * logFactor t := by
    intro i
    have hsplit := inverse_row_geometric_split (s.K t) hunit N
    have hentry (j : ι) : ‖s.P t i j‖ ≤
        (∑ k ∈ Finset.range N, ‖((s.K t) ^ k) i j‖) +
          ‖((s.K t) ^ N * s.P t) i j‖ := by
      change ‖(1 - s.K t)⁻¹ i j‖ ≤ _
      rw [hsplit, Matrix.add_apply]
      have hsum : (∑ k ∈ Finset.range N, (s.K t) ^ k) i j =
          ∑ k ∈ Finset.range N, ((s.K t) ^ k) i j :=
        Matrix.sum_apply i j (Finset.range N) (fun k => (s.K t) ^ k)
      rw [hsum]
      exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))
    calc
      ∑ j, ‖s.P t i j‖ ≤ ∑ j, ((∑ k ∈ Finset.range N, ‖((s.K t) ^ k) i j‖) +
          ‖((s.K t) ^ N * s.P t) i j‖) := Finset.sum_le_sum fun j _ => hentry j
      _ = (∑ k ∈ Finset.range N, ∑ j, ‖((s.K t) ^ k) i j‖) +
          (∑ j, ‖((s.K t) ^ N * s.P t) i j‖) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ (N : ℝ) * (C ^ 2 * E) + B * C ^ 2 := by
        apply add_le_add _ (htail i)
        calc
          (∑ k ∈ Finset.range N, ∑ j, ‖((s.K t) ^ k) i j‖) ≤
              ∑ k ∈ Finset.range N, C ^ 2 * E := Finset.sum_le_sum fun k hk => hshort k hk i
          _ = (N : ℝ) * (C ^ 2 * E) := by simp
      _ ≤ ((A + 1) * logFactor t) * (C ^ 2 * E) + B * C ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hN
          (by positivity : 0 ≤ C ^ 2 * E)) (le_refl _)
      _ ≤ Cout * logFactor t := by
        have htailScale : B * C ^ 2 ≤ B * C ^ 2 * logFactor t := by
          simpa using mul_le_mul_of_nonneg_left hlogF (by positivity : 0 ≤ B * C ^ 2)
        have hBScale : 0 ≤ B * logFactor t := by positivity
        dsimp [Cout]
        nlinarith
  refine ⟨hunit, ?_, ?_⟩
  · unfold rowNorm
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Cout * logFactor t)).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold l1; positivity)]
    exact hrow i
  · intro i j
    have hBC : B ≤ Cout := by
      have hnon : 0 ≤ C ^ 2 * E * (A + 1) + B * C ^ 2 := by positivity
      dsimp [Cout]
      linarith
    calc
      ‖s.P t i j‖ ≤ B * Real.exp (-(t ^ 3) * dist i j) := hPdecay i j
      _ ≤ Cout * Real.exp (-(t ^ 3) * dist i j) :=
        mul_le_mul_of_nonneg_right hBC (Real.exp_nonneg _)
      _ = Cout * Real.exp (-1 * t ^ 3 * dist i j) := by ring_nf

theorem inverse_row_proof : ∀ (d : ℕ) (C ρ β : ℝ), 1 ≤ C → 0 ≤ ρ → ρ < 1 → 0 < β →
    ∃ C' > 0, ∃ c > 0, ∃ t0 > 0, ∀ (n : ℕ) (t : ℝ)
    (s : State (Fin n)) (dist : Fin n → Fin n → ℝ),
    0 < t → t < t0 → ShellBounds d C dist → ‖s.K t‖ ≤ ρ → s.g.IsSymm →
    (∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C) → s.F t *ᵥ s.p = s.q →
    (∀ i, |s.q i - s.p i| ≤ C * power t β) →
    (∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t) →
    (∀ i j, C * power t (-2) < dist i j →
      ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C)) →
    IsUnit (1 - s.K t) ∧ rowNorm (s.P t) ≤ C' * logFactor t ∧
    (∀ i j, ‖s.P t i j‖ ≤ C' * Real.exp (-c * t^3 * dist i j)) := by
  intro d C ρ β hC hρ0 hρ1 hβ
  obtain ⟨Cout, hCout, c, hc, t0, ht0, h⟩ := inverse_row_finite d C ρ β hC hρ0 hρ1 hβ
  exact ⟨Cout, hCout, c, hc, t0, ht0, fun n => h (Fin n)⟩


private lemma prospective_small_power (e ε : ℝ) (he : 0 < e) (hε : 0 < ε) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 → power t e < ε := by
  refine ⟨power ε (1 / e), Real.rpow_pos_of_pos hε _, ?_⟩
  intro t ht hlt
  have hpow : power (power ε (1 / e)) e = ε := by
    dsimp [power]
    rw [← Real.rpow_mul hε.le]
    have hexp : (1 / e) * e = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  exact (Real.rpow_lt_rpow ht.le hlt he).trans_eq hpow

private lemma prospective_sum_subtype_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : S, f i.val) ≤ ∑ i, f i := by
  rw [← Finset.sum_subtype S (by intro i; rfl) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hf i)

private lemma prospective_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : CMat ι) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R) (i x : ι) :
    ∑ j, ‖h i j‖ * ‖h x j‖ ≤ R := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖h i j‖) (fun j => ‖h x j‖)
  have hi := hrow i
  have hx := hrow x
  have hprod : (∑ j, ‖h i j‖ ^ 2) * (∑ j, ‖h x j‖ ^ 2) ≤ R ^ 2 := by
    simpa [pow_two] using mul_le_mul hi hx (Finset.sum_nonneg fun j _ => sq_nonneg _) hR
  exact (sq_le_sq₀ (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hR).mp
    (hcs.trans hprod)

private lemma prospective_h_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) (ht : 0 < t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i j : survivors x, (deleteState t s x ξ).h t i j =
      s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val := by
  intro i j
  have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  change (Real.sqrt t : ℂ) *
    (s.g i.val j.val - ((ξ : ℂ) + t * s.r x) * s.g i.val x * s.g x j.val /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
    (Real.sqrt t : ℂ) * s.g i.val j.val -
      (((ξ : ℂ) + t * s.r x) /
        ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
        ((Real.sqrt t : ℂ) * s.g i.val x) * ((Real.sqrt t : ℂ) * s.g x j.val)
  field_simp [hden, hsqrt]

private lemma prospective_gamma {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t G : ℝ) (s : State ι) (x : ι) (ξ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hG : 1 ≤ G) (hsmall : Real.sqrt t < (4 * G ^ 2)⁻¹)
    (hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ G) (hξ : |ξ| ≤ G * Real.sqrt t) :
    (1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧ ‖gamma t s x ξ‖ ≤ 4 * G := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
  have hη : |ξ / Real.sqrt t| ≤ G := by
    rw [abs_div, abs_of_pos hsqrt, div_le_iff₀ hsqrt]
    exact hξ
  have hηeq : Real.sqrt t * (ξ / Real.sqrt t) = ξ := by field_simp
  have hb := gamma_pointwise_bounds G t (Real.sqrt t) (ξ / Real.sqrt t) ξ s x hG ht
    hsqrt hsqrt1 hsmall (Real.sq_sqrt ht.le) hηeq hη hstate
  exact ⟨hb.1, hb.2.1⟩

private lemma prospective_entry_small {n : ℕ} (t C : ℝ) (s : State (Fin n))
    (Λ W : Form (Fin n)) (hs : Prestate t C Λ W s) :
    ∀ i j, ‖s.h t i j‖ ≤ power t (1 / 4) := by
  intro i j
  have hfour : ‖s.h t i j‖ ^ 4 ≤ rowCap t :=
    (Finset.single_le_sum (fun k _ => pow_nonneg (norm_nonneg _) 4)
      (Finset.mem_univ j)).trans (hs.row_cap i)
  have hcap : rowCap t ≤ t := by
    calc
      rowCap t = power t (1 + delta) := rfl
      _ ≤ power t 1 := Real.rpow_le_rpow_of_exponent_ge hs.scale.1 hs.scale.2.le
        (by norm_num [delta])
      _ = t := Real.rpow_one _
  have hv : 0 ≤ power t (1 / 4) := Real.rpow_nonneg hs.scale.1.le _
  have hpow : (power t (1 / 4)) ^ 4 = t := by
    dsimp [power]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.scale.1.le]
    norm_num
  have hle : ‖s.h t i j‖ ^ 4 ≤ (power t (1 / 4)) ^ 4 := by rw [hpow]; exact hfour.trans hcap
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hv (by norm_num : (4 : ℕ) ≠ 0)).mp hle

private lemma prospective_sqrt_cap {t : ℝ} (ht : 0 < t) :
    Real.sqrt (rowCap t) / Real.sqrt t = power t (delta / 2) := by
  have hrowpos : 0 < rowCap t := Real.rpow_pos_of_pos ht _
  have hrowExp : t ^ (1 + delta) / t = t ^ delta := by
    calc
      t ^ (1 + delta) / t = t ^ (1 + delta) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 + delta) - 1) := (Real.rpow_sub ht (1 + delta) 1).symm
      _ = t ^ delta := by congr 1; ring
  have hleftsq : (Real.sqrt (rowCap t) / Real.sqrt t) ^ 2 = power t delta := by
    rw [div_pow, Real.sq_sqrt hrowpos.le, Real.sq_sqrt ht.le, rowCap, power]
    exact hrowExp
  have hrightsq : power t (delta / 2) ^ 2 = power t delta := by
    dsimp [power]
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hleftpos : 0 < Real.sqrt (rowCap t) / Real.sqrt t := by positivity
  have hrightpos : 0 < power t (delta / 2) := Real.rpow_pos_of_pos ht _
  nlinarith

private lemma prospective_K_delta_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (x : ι) (ξ G : ℝ) (hG : 0 ≤ G)
    (hγ : ‖gamma t s x ξ‖ ≤ G)
    (hupdate : ∀ i j : survivors x, (deleteState t s x ξ).h t i j =
      s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val) :
    ∀ i j : survivors x,
      ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤
        2 * G * ‖s.h t i.val x‖ * ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖ +
          G ^ 2 * ‖s.h t i.val x‖ ^ 2 * ‖s.h t x j.val‖ ^ 2 := by
  intro i j
  change ‖((deleteState t s x ξ).h t i j) ^ 2 - (s.h t i.val j.val) ^ 2‖ ≤ _
  rw [hupdate]
  have heq : (s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val) ^ 2 -
      (s.h t i.val j.val) ^ 2 =
      -2 * gamma t s x ξ * s.h t i.val x * s.h t i.val j.val * s.h t x j.val +
        (gamma t s x ξ) ^ 2 * (s.h t i.val x) ^ 2 * (s.h t x j.val) ^ 2 := by ring
  rw [heq]
  calc
    ‖_ + _‖ ≤ ‖-2 * gamma t s x ξ * s.h t i.val x * s.h t i.val j.val * s.h t x j.val‖ +
        ‖(gamma t s x ξ) ^ 2 * (s.h t i.val x) ^ 2 * (s.h t x j.val) ^ 2‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul, norm_pow, norm_neg]
      norm_num
      gcongr


private lemma prospective_delete_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) (hs : s.g.IsSymm) :
    (deleteState t s x ξ).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change s.g j.val i.val - ((ξ : ℂ) + t * s.r x) * s.g j.val x * s.g x i.val /
    (1 + ((ξ : ℂ) + t * s.r x) * s.g x x) =
    s.g i.val j.val - ((ξ : ℂ) + t * s.r x) * s.g i.val x * s.g x j.val /
    (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
  rw [hs.apply j.val i.val, hs.apply j.val x, hs.apply x i.val]
  ring

private lemma prospective_K_delta_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (s : State ι) (x : ι) (ξ G R v : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hγ : ‖gamma t s x ξ‖ ≤ G) (hsymm : s.g.IsSymm)
    (hrow : ∀ i, ∑ j, ‖s.h t i j‖ ^ 2 ≤ R) (hentry : ∀ i j, ‖s.h t i j‖ ≤ v)
    (hupdate : ∀ i j : survivors x, (deleteState t s x ξ).h t i j =
      s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val) :
    (∀ i : survivors x, ∑ j : survivors x,
      ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤ (2 * G + G ^ 2) * R * v) ∧
    (∀ j : survivors x, ∑ i : survivors x,
      ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖ ≤ (2 * G + G ^ 2) * R * v) := by
  classical
  have hprod (i : survivors x) : (∑ j : survivors x,
      ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖) ≤ R :=
    (prospective_sum_subtype_le (survivors x) _ (fun j => by positivity)).trans
      (prospective_row_product (s.h t) R hR hrow i.val x)
  have hxsum : (∑ j : survivors x, ‖s.h t x j.val‖ ^ 2) ≤ R :=
    (prospective_sum_subtype_le (survivors x) _ (fun j => sq_nonneg _)).trans (hrow x)
  have hrowDelta (i : survivors x) : (∑ j : survivors x,
      ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖) ≤ (2 * G + G ^ 2) * R * v := by
    have hi := hentry i.val x
    have hi2 : ‖s.h t i.val x‖ ^ 2 ≤ v := by
      have hiSq : ‖s.h t i.val x‖ ^ 2 ≤ v ^ 2 := (sq_le_sq₀ (norm_nonneg _) hv).2 hi
      nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]
    calc
      (∑ j : survivors x, ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖) ≤
          ∑ j : survivors x, (2 * G * ‖s.h t i.val x‖ * ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖ +
            G ^ 2 * ‖s.h t i.val x‖ ^ 2 * ‖s.h t x j.val‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => prospective_K_delta_entry t s x ξ G hG hγ hupdate i j
      _ = 2 * G * ‖s.h t i.val x‖ *
          (∑ j : survivors x, ‖s.h t i.val j.val‖ * ‖s.h t x j.val‖) +
          G ^ 2 * ‖s.h t i.val x‖ ^ 2 * (∑ j : survivors x, ‖s.h t x j.val‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ 2 * G * v * R + G ^ 2 * v * R := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) (hprod i)
            (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hi2 (sq_nonneg G)) hxsum
            (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      _ = (2 * G + G ^ 2) * R * v := by ring
  have hnewSym := prospective_delete_symm t s x ξ hsymm
  have hdeltaSym (i j : survivors x) :
      (deleteState t s x ξ).K t i j - s.K t i.val j.val =
        (deleteState t s x ξ).K t j i - s.K t j.val i.val := by
    simp only [State.K, entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare,
      State.h, Matrix.smul_apply, smul_eq_mul]
    rw [hnewSym.apply i j, hsymm.apply i.val j.val]
  refine ⟨hrowDelta, ?_⟩
  intro j
  calc
    (∑ i : survivors x, ‖(deleteState t s x ξ).K t i j - s.K t i.val j.val‖) =
        ∑ i : survivors x, ‖(deleteState t s x ξ).K t j i - s.K t j.val i.val‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdeltaSym]
    _ ≤ _ := hrowDelta j

private lemma prospective_restrict_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMat ι) (S : Finset ι) : ‖restrict A S‖ ≤ ‖A‖ := by
  classical
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro y
  let v : ι → ℂ := fun i => if hi : i ∈ S then y.ofLp ⟨i, hi⟩ else 0
  let z : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hz : ‖z‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖v i‖ ^ 2) = ∑ i : S, ‖y.ofLp i‖ ^ 2
    have hout : (∑ i ∈ S, ‖v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [v, hi]
    calc
      (∑ i, ‖v i‖ ^ 2) = ∑ i ∈ S, ‖v i‖ ^ 2 := hout.symm
      _ = ∑ i : S, ‖v i.val‖ ^ 2 := Finset.sum_subtype S (by intro i; rfl) _
      _ = ∑ i : S, ‖y.ofLp i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [v, i.property]
  have hrestrict (i : S) :
      (euclCLM (restrict A S) y).ofLp i = (euclCLM A z).ofLp i.val := by
    change (Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (restrict A S) y).ofLp i =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A z).ofLp i.val
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    change (∑ j : S, A i.val j.val * y.ofLp j) = ∑ j, A i.val j * v j
    have hout : (∑ j ∈ S, A i.val j * v j) = ∑ j, A i.val j * v j := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [v, hj]
    calc
      (∑ j : S, A i.val j.val * y.ofLp j) = ∑ j : S, A i.val j.val * v j.val := by
        apply Finset.sum_congr rfl
        intro j _
        simp [v, j.property]
      _ = ∑ j ∈ S, A i.val j * v j := (Finset.sum_subtype S (by intro j; rfl) (fun j => A i.val j * v j)).symm
      _ = ∑ j, A i.val j * v j := hout
  have hproj : ‖euclCLM (restrict A S) y‖ ≤ ‖euclCLM A z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hh : (∑ i : S, ‖(euclCLM (restrict A S) y).ofLp i‖ ^ 2) =
        ∑ i : S, ‖(euclCLM A z).ofLp i.val‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrestrict]
    rw [hh]
    exact prospective_sum_subtype_le S (fun i => ‖(euclCLM A z).ofLp i‖ ^ 2)
      (fun i => sq_nonneg _)
  calc
    ‖euclCLM (restrict A S) y‖ ≤ ‖euclCLM A z‖ := hproj
    _ ≤ ‖euclCLM A‖ * ‖z‖ := (euclCLM A).le_opNorm z
    _ = ‖A‖ * ‖y‖ := by
      have hnorm : ‖euclCLM A‖ = ‖A‖ := (Matrix.l2_opNorm_toEuclideanCLM A).symm
      rw [hz, hnorm]

private lemma prospective_diag_change {n : ℕ} (t C : ℝ) (s : State (Fin n))
    (Λ W : Form (Fin n)) (hs : Prestate t C Λ W s) (x : Fin n) (ξ G : ℝ)
    (hγ : ‖gamma t s x ξ‖ ≤ G) (hG : 0 ≤ G)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i : survivors x, ‖(deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤ G * power t beta := by
  intro i
  have ht := hs.scale.1
  have hroot := Real.sqrt_pos.2 ht
  have hupdate := prospective_h_update t s x ξ ht hden i i
  have hscale : (Real.sqrt t : ℂ) *
      ((deleteState t s x ξ).g i i - s.g i.val i.val) =
      -gamma t s x ξ * s.h t i.val x * s.h t x i.val := by
    change (Real.sqrt t : ℂ) * (deleteState t s x ξ).g i i =
      (Real.sqrt t : ℂ) * s.g i.val i.val -
        gamma t s x ξ * s.h t i.val x * s.h t x i.val at hupdate
    linear_combination hupdate
  have hsmall : ‖s.h t i.val x‖ ^ 2 ≤ Real.sqrt (rowCap t) := by
    have hfour : ‖s.h t i.val x‖ ^ 4 ≤ rowCap t :=
      (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 4)
        (Finset.mem_univ x)).trans (hs.row_cap i.val)
    have hrootSq : Real.sqrt (rowCap t) ^ 2 = rowCap t :=
      Real.sq_sqrt (Real.rpow_nonneg ht.le _)
    nlinarith [Real.sqrt_nonneg (rowCap t), sq_nonneg ‖s.h t i.val x‖]
  have hnorm : Real.sqrt t * ‖(deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤
      G * Real.sqrt (rowCap t) := by
    have heq := congrArg norm hscale
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hroot] at heq
    have hsymm : s.h t x i.val = s.h t i.val x := by simp [State.h, hs.symmetric.apply]
    rw [hsymm] at heq
    rw [heq]
    calc
      ‖gamma t s x ξ‖ * ‖s.h t i.val x‖ * ‖s.h t i.val x‖ =
          ‖gamma t s x ξ‖ * ‖s.h t i.val x‖ ^ 2 := by ring
      _ ≤ G * Real.sqrt (rowCap t) := mul_le_mul hγ hsmall (sq_nonneg _) hG
  calc
    ‖(deleteState t s x ξ).g i i - s.g i.val i.val‖ ≤ G * Real.sqrt (rowCap t) / Real.sqrt t :=
      (le_div_iff₀ hroot).2 (by simpa [mul_comm] using hnorm)
    _ = G * power t (delta / 2) := by rw [mul_div_assoc, prospective_sqrt_cap ht]
    _ ≤ G * power t beta := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht hs.scale.2.le (by norm_num [S45.beta, delta])) hG


private structure ProspectiveData {n : ℕ} (t B : ℝ) (s : State (Fin n)) (x : Fin n) (ξ : ℝ) : Prop where
  den : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0
  gamma_bound : ‖gamma t s x ξ‖ ≤ 12 * B
  old_rows : ∀ i, ∑ j, s.F t i j ≤ B
  old_raw : ∀ i, ‖s.rawLag i‖ ≤ B * power t beta
  old_qp : ∀ i, |s.q i - s.p i| ≤ B * power t beta
  post_qp : ∀ i, |(deleteState t s x ξ).q i - (deleteState t s x ξ).p i| ≤ 13 * B * power t beta
  post_rows : ∀ i, ∑ j, (deleteState t s x ξ).F t i j ≤ 14 * B ^ 2
  post_ward : (deleteState t s x ξ).F t *ᵥ (deleteState t s x ξ).p = (deleteState t s x ξ).q
  post_symm : (deleteState t s x ξ).g.IsSymm
  post_cap : ‖(deleteState t s x ξ).K t‖ ≤ 3 / 4
  post_unit : IsUnit (1 - (deleteState t s x ξ).K t)

set_option maxHeartbeats 1200000 in
private theorem prospective_numerical : ∀ C : ℝ, 1 ≤ C →
    ∃ B, 1 ≤ B ∧ C ≤ B ∧ ∃ t0 > 0,
    ∀ (n : ℕ) (t : ℝ) (s : State (Fin n)) (Λ W : Form (Fin n)) (x : Fin n) (ξ : ℝ),
    t < t0 → Prestate t C Λ W s → |ξ| ≤ C * Real.sqrt t → ProspectiveData t B s x ξ := by
  intro C hC
  obtain ⟨R, hR, tr, htr, hpre⟩ := analytic_prestate_proof C hC
  let B : ℝ := 1 + C + R
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBC : C ≤ B := by dsimp [B]; linarith
  have hBR : R ≤ B := by dsimp [B]; linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨tg, htg, hg⟩ := prospective_small_power (1 / 2) ((4 * (3 * B) ^ 2)⁻¹)
    (by norm_num) (by positivity)
  let A : ℝ := (2 * (12 * B) + (12 * B) ^ 2) * B
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨tk, htk, hk⟩ := prospective_small_power (1 / 4) (1 / (4 * A))
    (by norm_num) (by positivity)
  refine ⟨B, hB, hBC, min tr (min tg tk), by positivity, ?_⟩
  intro n t s Λ W x ξ htt hs hξ
  have ht := hs.scale.1
  have ht1 := hs.scale.2.le
  have httR : t < tr := lt_of_lt_of_le htt (min_le_left _ _)
  have httg : t < tg := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have httk : t < tk := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  have hbroad := (hpre n t s Λ W httR hs).1
  have hpowβ : 0 ≤ power t beta := Real.rpow_nonneg ht.le _
  have hpowβ1 : power t beta ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num [S45.beta, delta])
  have hrows (i : Fin n) : ∑ j, s.F t i j ≤ B := (hbroad i).2.2.1.trans hBR
  have hraw (i : Fin n) : ‖s.rawLag i‖ ≤ B * power t beta :=
    (hbroad i).1.trans (mul_le_mul_of_nonneg_right hBR hpowβ)
  have hqp (i : Fin n) : |s.q i - s.p i| ≤ B * power t beta :=
    (hbroad i).2.1.trans (mul_le_mul_of_nonneg_right hBR hpowβ)
  have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ 3 * B := by
    have hr : ‖s.r x‖ ≤ B := (hs.broad x).1.trans hBC
    have hrawB : ‖s.rawLag x‖ ≤ B := (hraw x).trans (by nlinarith)
    have htri : ‖s.g x x‖ ≤ ‖s.r x‖ + ‖s.rawLag x‖ :=
      norm_le_insert' (s.g x x) (s.r x)
    linarith
  have hrootSmall : Real.sqrt t < (4 * (3 * B) ^ 2)⁻¹ := by
    simpa [power, Real.sqrt_eq_rpow] using hg t ht httg
  have hξB : |ξ| ≤ (3 * B) * Real.sqrt t := hξ.trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ 3 * B) (Real.sqrt_nonneg t))
  obtain ⟨hden, hgamma⟩ := prospective_gamma t (3 * B) s x ξ ht ht1 (by linarith)
    hrootSmall hstate hξB
  have hγ : ‖gamma t s x ξ‖ ≤ 12 * B := by nlinarith
  have hupdate := prospective_h_update t s x ξ ht hden
  have hentry := prospective_entry_small t C s Λ W hs
  have hv : 0 ≤ power t (1 / 4) := Real.rpow_nonneg ht.le _
  have hv1 : power t (1 / 4) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hsums := prospective_K_delta_sums t s x ξ (12 * B) B (power t (1 / 4))
    (by positivity) hBpos.le hv hv1 hγ hs.symmetric hrows hentry hupdate
  have hδ : ‖(deleteState t s x ξ).K t - restrict (s.K t) (survivors x)‖ ≤ 1 / 4 := by
    have hscale : A * power t (1 / 4) ≤ 1 / 4 := by
      have hlt := (lt_div_iff₀ (by positivity : 0 < 4 * A)).mp (hk t ht httk)
      nlinarith
    calc
      ‖(deleteState t s x ξ).K t - restrict (s.K t) (survivors x)‖ ≤
          Real.sqrt ((A * power t (1 / 4)) * (A * power t (1 / 4))) :=
        matrix_schur_opNorm_bound _ _ _ (by positivity) (by positivity) hsums.1 hsums.2
      _ = A * power t (1 / 4) := Real.sqrt_mul_self (by positivity)
      _ ≤ 1 / 4 := hscale
  have hcap : ‖(deleteState t s x ξ).K t‖ ≤ 3 / 4 := by
    calc
      ‖(deleteState t s x ξ).K t‖ ≤ ‖restrict (s.K t) (survivors x)‖ +
          ‖(deleteState t s x ξ).K t - restrict (s.K t) (survivors x)‖ := norm_le_insert' _ _
      _ ≤ ‖s.K t‖ + 1 / 4 := add_le_add (prospective_restrict_norm _ _) hδ
      _ ≤ 3 / 4 := by linarith [hs.K_cap]
  have hnewqp (i : survivors x) :
      |(deleteState t s x ξ).q i - (deleteState t s x ξ).p i| ≤ 13 * B * power t beta := by
    have hchange := prospective_diag_change t C s Λ W hs x ξ (12 * B) hγ (by positivity) hden i
    have htriangle : |(deleteState t s x ξ).q i - (deleteState t s x ξ).p i| ≤
        ‖(deleteState t s x ξ).g i i - s.g i.val i.val‖ + |s.q i.val - s.p i.val| := by
      have heq : (deleteState t s x ξ).q i - (deleteState t s x ξ).p i =
          ((deleteState t s x ξ).g i i - s.g i.val i.val).im + (s.q i.val - s.p i.val) := by
        simp [State.q, State.p, deleteState]
        ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (Complex.abs_im_le_norm _) (le_refl _))
    calc
      _ ≤ (12 * B) * power t beta + B * power t beta :=
        htriangle.trans (add_le_add hchange (hqp i.val))
      _ = 13 * B * power t beta := by ring
  have hward : (deleteState t s x ξ).F t *ᵥ (deleteState t s x ξ).p =
      (deleteState t s x ξ).q := by
    ext i
    simpa [State.F, entryAbsSquare, Matrix.mulVec, dotProduct, mul_comm, State.p, deleteState] using
      delete_diag_ward_row t s x ξ ht hs.symmetric hs.ward hden hupdate i
  have hpB (i : survivors x) : 1 / B ≤ (deleteState t s x ξ).p i ∧
      (deleteState t s x ξ).p i ≤ B := by
    change 1 / B ≤ s.p i.val ∧ s.p i.val ≤ B
    exact ⟨(one_div_le_one_div_of_le (by linarith : 0 < C) hBC).trans (hs.broad i.val).2.1,
      (hs.broad i.val).2.2.trans hBC⟩
  have hnewrows (i : survivors x) : ∑ j, (deleteState t s x ξ).F t i j ≤ 14 * B ^ 2 := by
    have hnewq : (deleteState t s x ξ).q i ≤ 14 * B := by
      have hh := (abs_le.mp (hnewqp i)).2
      have hp := (hpB i).2
      nlinarith
    have hFp := congrFun hward i
    change (∑ j, (deleteState t s x ξ).F t i j * (deleteState t s x ξ).p j) =
      (deleteState t s x ξ).q i at hFp
    calc
      (∑ j, (deleteState t s x ξ).F t i j) ≤
          ∑ j, B * ((deleteState t s x ξ).F t i j * (deleteState t s x ξ).p j) := by
        apply Finset.sum_le_sum
        intro j _
        have hpj := (div_le_iff₀ hBpos).mp (hpB j).1
        have hF : 0 ≤ (deleteState t s x ξ).F t i j := by simp [State.F, entryAbsSquare]
        nlinarith
      _ = B * (deleteState t s x ξ).q i := by rw [← Finset.mul_sum, hFp]
      _ ≤ 14 * B ^ 2 := by nlinarith
  exact ⟨hden, hγ, hrows, hraw, hqp, hnewqp, hnewrows, hward,
    prospective_delete_symm t s x ξ hs.symmetric, hcap,
    (inverse_row_contraction_inverse _ (3 / 4) hcap (by norm_num)).1⟩

end AndersonAC.AgentS45



