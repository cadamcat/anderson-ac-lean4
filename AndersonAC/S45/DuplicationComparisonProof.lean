import AndersonAC.S45.Definitions
import AndersonAC.S45.DuplicationProof
import AndersonAC.S45.SweepEndpointProof

/-! `AndersonAC.S45.duplication_comparison` (04-sweep.tex:89–125, the broad
comparisons `X₀ ≍ W*` and `D₀ ≍ W` of Lemma `duplication`). The dual
comparison follows from the exact duplication identity
(`duplication_proof`); the primal comparison follows by convex duality, with
an explicit optimal split for the spatial energy. Never imports
`Statements.lean`. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45
open AndersonAC.S45

namespace DupComparison

theorem qform_smul' {ι : Type*} [Fintype ι] (A : RMat ι) (r : ℝ) (v : ι → ℝ) :
    qform A (r • v) = r ^ 2 * qform A v := by
  simp only [qform, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem l2sq_real {ι : Type*} [Fintype ι] (f : ι → ℝ) : l2sq f = ∑ i, f i ^ 2 := by
  simp [l2sq, Real.norm_eq_abs, sq_abs]

theorem l2sq_nonneg'' {ι : Type*} [Fintype ι] (f : ι → ℝ) : 0 ≤ l2sq f := by
  rw [l2sq_real]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mulVec_one_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : RMat ι)
    (hA : constantKernel A) : A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hherm : A.IsHermitian := by
    show Aᴴ = A
    rw [conjTranspose_eq_transpose_of_trivial]; exact hA.1
  have hpsd : A.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun x => by
      simpa [qform, dotProduct] using hA.2.1 x)
  have hq : qform A (fun _ => 1) = 0 := (hA.2.2 _).2 ⟨1, fun _ => rfl⟩
  exact (hpsd.dotProduct_mulVec_zero_iff).1 (by simpa [qform, dotProduct] using hq)

theorem sum_mulVec_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : RMat ι)
    (hA : constantKernel A) (f : ι → ℝ) : ∑ i, (A *ᵥ f) i = 0 := by
  have h1 : ∑ i, (A *ᵥ f) i = (fun _ => (1 : ℝ)) ⬝ᵥ (A *ᵥ f) := by simp [dotProduct]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose, hA.1.eq, mulVec_one_eq_zero A hA,
    zero_dotProduct]

/-- Fenchel–Young and its equality case for a constant-kernel quadratic form. -/
theorem qform_fenchel {ι : Type*} [Fintype ι] [DecidableEq ι] (D : RMat ι)
    (hD : constantKernel D) (y : ι → ℝ) (hy : neutral y) (g : ι → ℝ) :
    2 * (∑ i, y i * g i) - qform D g ≤ dualForm (qform D) y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : (∑ i, y i * g i) = 0 := by simp
    rw [this]
    have h0 : qform D g = 0 := by simp [qform]
    rw [h0]; simpa using dualForm_qform_nonneg D y
  · obtain ⟨z, hz, -⟩ := exists_solution_constantKernel hD y hy
    rw [dualForm_eq_of_solve D hD.1 hD.2.1 y z hz]
    have h := hD.2.1 (g - z)
    rw [qform_sub_formula D hD.1 g z, hz] at h
    have hzz : qform D z = ∑ i, y i * z i := by
      simp only [qform, hz]; exact Finset.sum_congr rfl fun i _ => by ring
    have hgy : (∑ i, g i * y i) = ∑ i, y i * g i :=
      Finset.sum_congr rfl fun i _ => by ring
    linarith

theorem qform_bidual {ι : Type*} [Fintype ι] [DecidableEq ι] (D : RMat ι)
    (hD : constantKernel D) (f : ι → ℝ) :
    neutral (D *ᵥ f) ∧ qform D f = 2 * (∑ i, (D *ᵥ f) i * f i) - dualForm (qform D) (D *ᵥ f) := by
  refine ⟨sum_mulVec_eq_zero D hD f, ?_⟩
  rw [dualForm_eq_of_solve D hD.1 hD.2.1 (D *ᵥ f) f rfl]
  have : qform D f = ∑ i, (D *ᵥ f) i * f i := by
    simp only [qform]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

section Spatial

variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

/-- The decomposition set defining `spatialEnergy`. -/
def splitSet (site : P → I) (b : ℝ) (A : RMat I) (f : P → ℝ) : Set ℝ :=
  {a : ℝ | ∃ α : P → ℝ, ∃ u : I → ℝ,
    (∀ x, f x = α x + u (site x)) ∧ a = l2sq α + qform A u / b}

theorem spatialEnergy_eq (site : P → I) (b : ℝ) (A : RMat I) (f : P → ℝ) :
    spatialEnergy site b (qform A) f = sInf (splitSet site b A f) := rfl

theorem splitSet_nonempty (site : P → I) (b : ℝ) (A : RMat I) (f : P → ℝ) :
    (splitSet site b A f).Nonempty :=
  ⟨l2sq f + qform A 0 / b, f, 0, fun x => by simp, rfl⟩

theorem E_le (site : P → I) {b : ℝ} (hb : 0 < b) (A : RMat I) (hA : constantKernel A)
    (f α : P → ℝ) (u : I → ℝ) (hf : ∀ x, f x = α x + u (site x)) :
    spatialEnergy site b (qform A) f ≤ l2sq α + qform A u / b := by
  rw [spatialEnergy_eq]
  refine csInf_le ⟨0, ?_⟩ ⟨α, u, hf, rfl⟩
  rintro a ⟨α', u', -, rfl⟩
  exact add_nonneg (l2sq_nonneg'' _) (div_nonneg (hA.2.1 _) hb.le)

theorem E_ge (site : P → I) (b : ℝ) (A : RMat I) (f : P → ℝ) (c : ℝ)
    (h : ∀ α u, (∀ x, f x = α x + u (site x)) → c ≤ l2sq α + qform A u / b) :
    c ≤ spatialEnergy site b (qform A) f := by
  rw [spatialEnergy_eq]
  refine le_csInf (splitSet_nonempty site b A f) ?_
  rintro a ⟨α, u, hf, rfl⟩
  exact h α u hf

theorem E_scale (site : P → I) {b : ℝ} (hb : 0 < b) (A : RMat I) (hA : constantKernel A)
    (f : P → ℝ) {c : ℝ} (hc : 0 < c) :
    spatialEnergy site b (qform A) (c • f) ≤ c ^ 2 * spatialEnergy site b (qform A) f := by
  have hc2 : 0 < c ^ 2 := by positivity
  have h : spatialEnergy site b (qform A) (c • f) / c ^ 2 ≤
      spatialEnergy site b (qform A) f := by
    refine E_ge site b A f _ fun α u hf => ?_
    have hcf : ∀ x, (c • f) x = (c • α) x + (c • u) (site x) := fun x => by
      simp [hf x, mul_add]
    have := E_le site hb A hA (c • f) (c • α) (c • u) hcf
    rw [div_le_iff₀ hc2]
    calc spatialEnergy site b (qform A) (c • f) ≤ l2sq (c • α) + qform A (c • u) / b := this
      _ = (l2sq α + qform A u / b) * c ^ 2 := by
        rw [qform_smul', l2sq_real, l2sq_real]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
  rwa [div_le_iff₀ hc2, mul_comm] at h

theorem sum_site (site : P → I) (y : P → ℝ) (u : I → ℝ) :
    (∑ x, y x * u (site x)) = ∑ i, (∑ x, if site x = i then y x else 0) * u i := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (site x)]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

/-- Upper bound for the spatial dual set (so its `sSup` is a genuine supremum). -/
theorem E_dual_bound (site : P → I) {b : ℝ} (hb : 0 < b) (A : RMat I)
    (hA : constantKernel A) (y : P → ℝ) (hy : neutral y) :
    ∃ M, ∀ g, 2 * (∑ x, y x * g x) - spatialEnergy site b (qform A) g ≤ M := by
  set Y : I → ℝ := fun i => ∑ x, if site x = i then y x else 0 with hYdef
  have hY : neutral Y := by
    unfold neutral at hy ⊢
    rw [Finset.sum_comm]; simpa using hy
  rcases isEmpty_or_nonempty I with hI | hI
  · haveI : IsEmpty P := ⟨fun x => isEmptyElim (site x)⟩
    refine ⟨0, fun g => ?_⟩
    have h0 : (∑ x, y x * g x) = 0 := by simp
    rw [h0]
    have := E_ge site b A g 0 fun α u _ => by
      simp [l2sq, qform]
    linarith
  · obtain ⟨z, hz, -⟩ := exists_solution_constantKernel hA Y hY
    refine ⟨l2sq y + b * qform A z, fun g => ?_⟩
    have hEg := E_ge site b A g (2 * (∑ x, y x * g x) - (l2sq y + b * qform A z))
      fun α u hf => ?_
    · linarith
    · have hpair : (∑ x, y x * g x) = (∑ x, y x * α x) + ∑ i, Y i * u i := by
        rw [← sum_site site y u, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by rw [hf x]; ring
      have hα : 2 * (∑ x, y x * α x) - l2sq α ≤ l2sq y := by
        rw [l2sq_real, l2sq_real]
        have : 0 ≤ ∑ x, (y x - α x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hexp : (∑ x, (y x - α x) ^ 2) =
            (∑ x, y x ^ 2) - 2 * (∑ x, y x * α x) + ∑ x, α x ^ 2 := by
          simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1; congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
        linarith
      have hu : 2 * (∑ i, Y i * u i) - qform A u / b ≤ b * qform A z := by
        have h := hA.2.1 (u - b • z)
        rw [qform_sub_formula A hA.1 u (b • z), qform_smul', Matrix.mulVec_smul, hz] at h
        have hsum : (∑ i, u i * (b • Y) i) = b * ∑ i, Y i * u i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [hsum] at h
        rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
        have hb' : 0 < b⁻¹ := inv_pos.2 hb
        have key : 2 * (∑ i, Y i * u i) * b ≤ qform A u + b ^ 2 * qform A z := by linarith
        have := mul_le_mul_of_nonneg_right key hb'.le
        rw [mul_assoc, mul_inv_cancel₀ hb.ne', mul_one, add_mul] at this
        have hb2 : b ^ 2 * qform A z * b⁻¹ = b * qform A z := by field_simp
        linarith
      linarith

theorem E_fenchel (site : P → I) {b : ℝ} (hb : 0 < b) (A : RMat I)
    (hA : constantKernel A) (y : P → ℝ) (hy : neutral y) (g : P → ℝ) :
    2 * (∑ x, y x * g x) - spatialEnergy site b (qform A) g ≤
      dualForm (spatialEnergy site b (qform A)) y := by
  obtain ⟨M, hM⟩ := E_dual_bound site hb A hA y hy
  refine le_csSup ⟨M, ?_⟩ ⟨g, rfl⟩
  rintro a ⟨g', rfl⟩
  exact hM g'

/-- The nontrivial direction of spatial biduality, by an explicit optimal split. -/
theorem E_bidual (site : P → I) {b : ℝ} (hb : 0 < b) (A : RMat I)
    (hA : constantKernel A) (hsite : ∀ i, ∃ x, site x = i) (f : P → ℝ) :
    ∃ α : P → ℝ, neutral α ∧ spatialEnergy site b (qform A) f ≤
      2 * (∑ x, α x * f x) - dualForm (spatialEnergy site b (qform A)) α := by
  set N : I → ℝ := fun i => ∑ x, if site x = i then (1 : ℝ) else 0 with hNdef
  have hN : ∀ i, 1 ≤ N i := by
    intro i
    obtain ⟨x, hx⟩ := hsite i
    have h1 : (if site x = i then (1 : ℝ) else 0) ≤ N i :=
      Finset.single_le_sum (f := fun x => if site x = i then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ x)
    simpa [hx] using h1
  set G : RMat I := diagonal N + b⁻¹ • A with hGdef
  have hGq : ∀ w, (∑ i, w i * (G *ᵥ w) i) = (∑ i, N i * w i ^ 2) + b⁻¹ * qform A w := by
    intro w
    simp only [hGdef, Matrix.add_mulVec, Matrix.smul_mulVec, mulVec_diagonal, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, qform, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  have hinj : Function.Injective G.mulVec := by
    intro w1 w2 hw
    have h0 : G *ᵥ (w1 - w2) = 0 := by rw [Matrix.mulVec_sub, hw, sub_self]
    have hq := hGq (w1 - w2)
    rw [h0] at hq
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hq
    have hA0 : 0 ≤ b⁻¹ * qform A (w1 - w2) := mul_nonneg (inv_pos.2 hb).le (hA.2.1 _)
    have hterm : ∀ i, 0 ≤ N i * (w1 - w2) i ^ 2 := fun i =>
      mul_nonneg (le_trans zero_le_one (hN i)) (sq_nonneg _)
    have hS0 : (∑ i, N i * (w1 - w2) i ^ 2) = 0 := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 hS0 i (Finset.mem_univ _)
    have hNi : N i ≠ 0 := by linarith [hN i]
    have : (w1 - w2) i ^ 2 = 0 := by
      rcases mul_eq_zero.1 hi with h | h
      · exact absurd h hNi
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simpa [sub_eq_zero] using this
  have hsurj : Function.Surjective G.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  set r : I → ℝ := fun i => ∑ x, if site x = i then f x else 0 with hrdef
  obtain ⟨u, hu⟩ := hsurj r
  set α : P → ℝ := fun x => f x - u (site x) with hαdef
  -- the charge of `α` above each site is `A u / b`
  have hpush : ∀ i, (∑ x, if site x = i then α x else 0) = b⁻¹ * (A *ᵥ u) i := by
    intro i
    have hGi := congrFun hu i
    simp only [hGdef, Matrix.add_mulVec, Matrix.smul_mulVec, mulVec_diagonal, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hGi
    have hsplit : (∑ x, if site x = i then α x else 0) =
        r i - N i * u i := by
      simp only [hrdef, hNdef, hαdef, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · rw [h]; ring
      · ring
    rw [hsplit]; linarith
  have hαneutral : neutral α := by
    have h1 : (∑ x, α x) = ∑ i, ∑ x, if site x = i then α x else 0 := by
      rw [Finset.sum_comm]; simp
    unfold neutral
    rw [h1]
    simp only [hpush, ← Finset.mul_sum, sum_mulVec_eq_zero A hA u, mul_zero]
  have hdecomp : ∀ x, f x = α x + u (site x) := fun x => by simp [hαdef]
  have hEf := E_le site hb A hA f α u hdecomp
  -- `Σ α (u ∘ site) = Λ(u)/b`
  have hαu : (∑ x, α x * u (site x)) = qform A u / b := by
    rw [sum_site site α u]
    simp only [hpush, qform, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the dual value at `α` is at most `|α|² + Λ(u)/b`
  have hdual : dualForm (spatialEnergy site b (qform A)) α ≤ l2sq α + qform A u / b := by
    refine csSup_le ⟨_, ⟨f, rfl⟩⟩ ?_
    rintro a ⟨g, rfl⟩
    have hg := E_ge site b A g (2 * (∑ x, α x * g x) - (l2sq α + qform A u / b))
      fun β w hgw => ?_
    · linarith
    · have hpair : (∑ x, α x * g x) = (∑ x, α x * β x) + ∑ x, α x * w (site x) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by rw [hgw x]; ring
      have hβ : 2 * (∑ x, α x * β x) - l2sq β ≤ l2sq α := by
        rw [l2sq_real, l2sq_real]
        have : 0 ≤ ∑ x, (α x - β x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hexp : (∑ x, (α x - β x) ^ 2) =
            (∑ x, α x ^ 2) - 2 * (∑ x, α x * β x) + ∑ x, β x ^ 2 := by
          simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1; congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
        linarith
      have hw : 2 * (∑ x, α x * w (site x)) - qform A w / b ≤ qform A u / b := by
        rw [sum_site site α w]
        simp only [hpush]
        have h := hA.2.1 (w - u)
        rw [qform_sub_formula A hA.1 w u] at h
        have hsum : (∑ i, b⁻¹ * (A *ᵥ u) i * w i) = b⁻¹ * ∑ i, w i * (A *ᵥ u) i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum, div_eq_mul_inv, div_eq_mul_inv]
        have hb' : 0 < b⁻¹ := inv_pos.2 hb
        nlinarith [mul_le_mul_of_nonneg_left h hb'.le]
      linarith
  refine ⟨α, hαneutral, ?_⟩
  have hαf : (∑ x, α x * f x) = l2sq α + qform A u / b := by
    rw [← hαu, l2sq_real, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hdecomp x]; ring
  linarith

end Spatial

theorem div_wp_le {C a q z : ℝ} (hC : 0 < C) (ha : 1 / C ≤ a) (hq : 1 / C ≤ q) (hz : 0 ≤ z) :
    z / (a ^ 4 * q ^ 2) ≤ C ^ 6 * z := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have h1 : 1 ≤ C * a := by rw [div_le_iff₀ hC] at ha; linarith
  have h2 : 1 ≤ C * q := by rw [div_le_iff₀ hC] at hq; linarith
  have hF : 1 ≤ (C * a) ^ 4 * (C * q) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  rw [div_le_iff₀ (by positivity)]
  calc z = z * 1 := (mul_one z).symm
    _ ≤ z * ((C * a) ^ 4 * (C * q) ^ 2) := mul_le_mul_of_nonneg_left hF hz
    _ = C ^ 6 * z * (a ^ 4 * q ^ 2) := by ring

theorem le_div_wp {C a q z : ℝ} (ha0 : 0 < a) (ha : a ≤ 1) (hq0 : 0 < q) (hq : q ≤ C)
    (hz : 0 ≤ z) : z ≤ C ^ 2 * (z / (a ^ 4 * q ^ 2)) := by
  have hpos : 0 < a ^ 4 * q ^ 2 := by positivity
  have hle : a ^ 4 * q ^ 2 ≤ C ^ 2 := by
    have h4 : a ^ 4 ≤ 1 := pow_le_one₀ ha0.le ha
    have h2 : q ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hq0.le hq 2
    calc a ^ 4 * q ^ 2 ≤ 1 * C ^ 2 :=
          mul_le_mul h4 h2 (by positivity) zero_le_one
      _ = C ^ 2 := one_mul _
  have hd : 0 ≤ z / (a ^ 4 * q ^ 2) := div_nonneg hz hpos.le
  calc z = z / (a ^ 4 * q ^ 2) * (a ^ 4 * q ^ 2) := by field_simp
    _ ≤ z / (a ^ 4 * q ^ 2) * C ^ 2 := mul_le_mul_of_nonneg_left hle hd
    _ = C ^ 2 * (z / (a ^ 4 * q ^ 2)) := mul_comm _ _

end DupComparison

open DupComparison in
theorem duplication_comparison_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0,
    ∀ (n m : ℕ) (v : PortMap (Fin n) (Fin m)) (s : State (Fin m))
    (t b : ℝ) (Λ Λplus : Form (Fin m)),
    0 < t → 0 < b → (∀ i, v.mass i = 1) →
    (∀ x, 1 / C ≤ v.weight x ∧ v.weight x ≤ 1) →
    (∀ i, s.g i i = s.r i ∧ 1 / C ≤ s.p i ∧ s.p i ≤ C) →
    constantKernel (s.D t) →
    (∀ y, neutral y →
      (l2sq y + b * Λplus y) / C ≤ s.X t y ∧ s.X t y ≤ C * (l2sq y + b * Λplus y)) →
    (∀ y, neutral y → dualForm (spatialEnergy v.site b Λ) y = spatialDual v b Λplus y) →
    (∃ A : RMat (Fin m), Λ = qform A ∧ constantKernel A) →
    (∀ y, neutral y → 0 ≤ Λplus y) →
    let s0 := v.liftState s
    (∀ y, neutral y → spatialDual v b Λplus y / C' ≤ s0.X t y ∧
      s0.X t y ≤ C' * spatialDual v b Λplus y) ∧
    formComparable (qform (s0.D t)) (spatialEnergy v.site b Λ) C' := by
  intro C hC
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  set K : ℝ := 2 * C ^ 9 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro n m v s t b Λ Λplus ht hb hmass hw hs hker hX hdualE hΛ hΛplus
  obtain ⟨A, rfl, hA⟩ := hΛ
  intro s0
  have hinvC : 0 < 1 / C := by positivity
  have hk : ∀ x, 0 < v.weight x := fun x => lt_of_lt_of_le hinvC (hw x).1
  have hfix : ∀ i, s.g i i = s.r i := fun i => (hs i).1
  have hp : ∀ i, 0 < s.p i := fun i => lt_of_lt_of_le hinvC (hs i).2.1
  obtain ⟨-, -, -, -, hQid, hXid⟩ := duplication_proof v s t hmass hk hfix hker hp
  have hsymD0 := lift_D_isSymm v s t hfix hker
  have hD0 : constantKernel (s0.D t) := lifted_kernel v s t hmass hk hp hker hsymD0 hQid
  have hsite : ∀ i, ∃ x, v.site x = i := by
    intro i
    by_contra hnone
    push_neg at hnone
    have h := hmass i
    unfold PortMap.mass at h
    rw [Finset.sum_eq_zero fun x _ => if_neg (hnone x)] at h
    norm_num at h
  -- powers of C
  have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
  have hC3 : 1 ≤ C ^ 3 := one_le_pow₀ hC
  have hC6 : 1 ≤ C ^ 6 := one_le_pow₀ hC
  have hC9 : C ^ 9 = C ^ 3 * C ^ 6 := by ring
  have hC6le : C ^ 6 ≤ C ^ 9 := by rw [hC9]; nlinarith
  have hCle : C ≤ C ^ 9 := by
    have : C ^ 9 = C * C ^ 8 := by ring
    rw [this]; nlinarith [one_le_pow₀ (n := 8) hC]
  have hC2le : C ^ 2 ≤ C ^ 9 := by
    have : C ^ 9 = C ^ 2 * C ^ 7 := by ring
    rw [this]; nlinarith [one_le_pow₀ (n := 7) hC]
  have hC5le : C ^ 5 ≤ C ^ 9 := by
    have : C ^ 9 = C ^ 5 * C ^ 4 := by ring
    rw [this]; nlinarith [one_le_pow₀ (n := 4) hC, one_le_pow₀ (n := 5) hC]
  -- Part 1: the dual comparison
  have hpart1 : ∀ y, neutral y → spatialDual v b Λplus y / K ≤ s0.X t y ∧
      s0.X t y ≤ K * spatialDual v b Λplus y := by
    intro y hy
    set Y := v.sumCharge y with hYdef
    have hYn : neutral Y := sumCharge_neutral v y hy
    set T := ∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) with hTdef
    set S := ∑ i, Y i ^ 2 / s.p i ^ 2 with hSdef
    have hX0 : s0.X t y = s.X t Y + T - S := hXid y hy
    have hST : S ≤ T := port_weighted_charge_bound v s hmass hk hp y
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hTup : T ≤ C ^ 6 * l2sq y := by
      rw [l2sq_real, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ =>
        div_wp_le hC0 (hw x).1 (hs (v.site x)).2.1 (sq_nonneg _)
    have hTlow : l2sq y ≤ C ^ 2 * T := by
      rw [l2sq_real, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ =>
        le_div_wp (hk x) (hw x).2 (hp _) (hs (v.site x)).2.2 (sq_nonneg _)
    have hSlow : l2sq Y ≤ C ^ 2 * S := by
      rw [l2sq_real, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := le_div_wp one_pos le_rfl (hp i) (hs i).2.2 (sq_nonneg (Y i))
      simpa using this
    have hSup : S ≤ C ^ 2 * l2sq Y := by
      rw [l2sq_real, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : 1 ≤ C * s.p i := by
        have := (hs i).2.1; rw [div_le_iff₀ hC0] at this; linarith
      have hF : 1 ≤ (C * s.p i) ^ 2 := one_le_pow₀ h1
      have hpi := hp i
      rw [div_le_iff₀ (by positivity)]
      calc Y i ^ 2 = Y i ^ 2 * 1 := (mul_one _).symm
        _ ≤ Y i ^ 2 * (C * s.p i) ^ 2 := mul_le_mul_of_nonneg_left hF (sq_nonneg _)
        _ = C ^ 2 * Y i ^ 2 * s.p i ^ 2 := by ring
    have hΛY : 0 ≤ b * Λplus Y := mul_nonneg hb.le (hΛplus Y hYn)
    have hlY : 0 ≤ l2sq Y := l2sq_nonneg'' Y
    have hly : 0 ≤ l2sq y := l2sq_nonneg'' y
    obtain ⟨hXlo, hXhi⟩ := hX Y hYn
    rw [div_le_iff₀ hC0] at hXlo
    have hsd : spatialDual v b Λplus y = l2sq y + b * Λplus Y := rfl
    rw [hsd, hX0]
    constructor
    · rw [div_le_iff₀ hK]
      -- l2sq y + bΛ ≤ C²(T - S) + (C⁴ + 1)·C·sX
      have h1 : l2sq y ≤ C ^ 2 * (T - S) + C ^ 2 * (C ^ 2 * l2sq Y) := by
        have := mul_le_mul_of_nonneg_left hSup (by positivity : (0:ℝ) ≤ C ^ 2)
        nlinarith
      have hsX : 0 ≤ s.X t Y := dualForm_qform_nonneg _ _
      have h2 : C ^ 2 * (C ^ 2 * l2sq Y) + b * Λplus Y ≤ (C ^ 4 + 1) * (C * s.X t Y) := by
        have e1 : C ^ 2 * (C ^ 2 * l2sq Y) = C ^ 4 * l2sq Y := by ring
        rw [e1]
        have h4 : C ^ 4 * l2sq Y ≤ C ^ 4 * (l2sq Y + b * Λplus Y) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h5 : C ^ 4 * (l2sq Y + b * Λplus Y) + (l2sq Y + b * Λplus Y) =
            (C ^ 4 + 1) * (l2sq Y + b * Λplus Y) := by ring
        have h6 : (C ^ 4 + 1) * (l2sq Y + b * Λplus Y) ≤ (C ^ 4 + 1) * (C * s.X t Y) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have h3 : C ^ 2 * (T - S) ≤ K * (T - S) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith); rw [hKdef]; linarith
      have h4 : (C ^ 4 + 1) * (C * s.X t Y) ≤ K * s.X t Y := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ hsX
        have : (C ^ 4 + 1) * C = C ^ 5 + C := by ring
        rw [this, hKdef]; linarith
      have h7 : (s.X t Y + T - S) * K = K * (T - S) + K * s.X t Y := by ring
      rw [h7]; linarith
    · have h1 : s.X t Y ≤ C * l2sq Y + C * (b * Λplus Y) := by linarith [mul_add C (l2sq Y) (b * Λplus Y)]
      have h2 : C * l2sq Y ≤ C ^ 3 * T := by
        have := mul_le_mul_of_nonneg_left (hSlow.trans (mul_le_mul_of_nonneg_left hST (by positivity))) hC0.le
        have e : C * (C ^ 2 * T) = C ^ 3 * T := by ring
        linarith
      have h3 : (C ^ 3 + 1) * T ≤ K * l2sq y := by
        have hT0 : 0 ≤ T := le_trans hS0 hST
        have a1 := mul_le_mul_of_nonneg_left hTup (by positivity : (0:ℝ) ≤ C ^ 3 + 1)
        have a2 : (C ^ 3 + 1) * (C ^ 6 * l2sq y) = (C ^ 9 + C ^ 6) * l2sq y := by ring
        have a3 : (C ^ 9 + C ^ 6) * l2sq y ≤ K * l2sq y := by
          apply mul_le_mul_of_nonneg_right _ hly; rw [hKdef]; linarith
        linarith
      have h4 : C * (b * Λplus Y) ≤ K * (b * Λplus Y) := by
        apply mul_le_mul_of_nonneg_right _ hΛY; rw [hKdef]; linarith
      have h5 : K * (l2sq y + b * Λplus Y) = K * l2sq y + K * (b * Λplus Y) := by ring
      have h6 : (C ^ 3 + 1) * T = C ^ 3 * T + T := by ring
      rw [h5]; linarith
  refine ⟨hpart1, fun f => ⟨?_, ?_⟩⟩
  · -- E f / K ≤ Q f
    rw [div_le_iff₀ hK]
    obtain ⟨α, hαn, hEα⟩ := E_bidual v.site hb A hA hsite f
    have hEd : dualForm (spatialEnergy v.site b (qform A)) α = spatialDual v b Λplus α :=
      hdualE α hαn
    have hup := (hpart1 α hαn).2
    have hfen : 2 * (∑ x, α x * (K • f) x) - qform (s0.D t) (K • f) ≤ s0.X t α :=
      qform_fenchel (s0.D t) hD0 α hαn (K • f)
    rw [qform_smul'] at hfen
    have hsum : (∑ x, α x * (K • f) x) = K * ∑ x, α x * f x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by simp; ring
    rw [hsum] at hfen
    -- spatialDual α ≥ X0 α / K ≥ 2Σαf - K Q f
    have hd : 2 * (∑ x, α x * f x) - K * qform (s0.D t) f ≤ spatialDual v b Λplus α := by
      rw [← mul_le_mul_iff_of_pos_left hK]
      have e : K * (2 * (∑ x, α x * f x) - K * qform (s0.D t) f) =
          2 * (K * ∑ x, α x * f x) - K ^ 2 * qform (s0.D t) f := by ring
      linarith
    have e2 : qform (s0.D t) f * K = K * qform (s0.D t) f := mul_comm _ _
    linarith
  · -- Q f ≤ K * E f
    obtain ⟨hyn, hQ⟩ := qform_bidual (s0.D t) hD0 f
    set y := s0.D t *ᵥ f with hydef
    have hEd : dualForm (spatialEnergy v.site b (qform A)) y = spatialDual v b Λplus y :=
      hdualE y hyn
    have hlo := (hpart1 y hyn).1
    have hfen := E_fenchel v.site hb A hA y hyn (K • f)
    have hsc := E_scale v.site hb A hA f hK
    have hsum : (∑ x, y x * (K • f) x) = K * ∑ x, y x * f x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by simp; ring
    rw [hsum, hEd] at hfen
    have hX0 : s0.X t y = dualForm (qform (s0.D t)) y := rfl
    have hd : 2 * (∑ x, y x * f x) - K * spatialEnergy v.site b (qform A) f ≤
        spatialDual v b Λplus y / K := by
      rw [le_div_iff₀ hK]
      have e : (2 * (∑ x, y x * f x) - K * spatialEnergy v.site b (qform A) f) * K =
          2 * (K * ∑ x, y x * f x) - K ^ 2 * spatialEnergy v.site b (qform A) f := by ring
      linarith
    rw [hX0] at hlo
    linarith

end AndersonAC.AgentS45
