import AndersonAC.AgentS6Row.CrossUpdate
import AndersonAC.AgentS6Row.Predictable

noncomputable section
open Matrix Finset ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

variable {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]

/-- Normalized inner product written without choosing a square root. -/
def rowPair (C : Matrix R B ℂ) (τ : ℝ) (x i : R) : ℂ :=
  C x ⬝ᵥ ((ridgeGram C τ)⁻¹ *ᵥ star (C i))

/-- The contraction with the heat Gram vector, written through the inverse Gram. -/
def rowBPair (C : Matrix R B ℂ) (τ : ℝ) (T : Finset R) (v : R → ℂ) (i : R) : ℂ :=
  C i ⬝ᵥ ((ridgeGram C τ)⁻¹ *ᵥ (∑ j ∈ T, v j • star (C j)))

lemma normalized_rowPair (C : Matrix R B ℂ) (τ : ℝ) (L : Matrix B B ℂ)
    (hL : L * Lᴴ = (ridgeGram C τ)⁻¹) (x i : R) :
    (C x ᵥ* L) ⬝ᵥ star (C i ᵥ* L) = rowPair C τ x i := by
  rw [star_vecMul, dotProduct_vecMul', Matrix.mulVec_mulVec, hL]
  rfl

lemma normalized_rowBPair (C : Matrix R B ℂ) (τ : ℝ) (L : Matrix B B ℂ)
    (hL : L * Lᴴ = (ridgeGram C τ)⁻¹) (T : Finset R) (v : R → ℂ) (i : R) :
    (C i ᵥ* L) ⬝ᵥ (∑ j ∈ T, v j • star (C j ᵥ* L)) = rowBPair C τ T v i := by
  have hb : (∑ j ∈ T, v j • star (C j ᵥ* L)) = Lᴴ *ᵥ (∑ j ∈ T, v j • star (C j)) := by
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [star_vecMul, Matrix.mulVec_smul]
  rw [hb, dotProduct_vecMul', Matrix.mulVec_mulVec, hL]
  rfl

lemma measurable_ridgeGram :
    Measurable (fun p : Matrix R B ℂ × ℝ => ridgeGram p.1 p.2) :=
  (Continuous.add (continuous_fst.matrix_conjTranspose.matrix_mul continuous_fst)
    ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)).measurable

lemma measurable_rowBPair {Ω : Type*} [MeasurableSpace Ω]
    (C : Ω → Matrix R B ℂ) (τ : Ω → ℝ) (v : Ω → R → ℂ)
    (hC : Measurable C) (hτ : Measurable τ) (hv : Measurable v)
    (T : Finset R) (i : R) : Measurable (fun ω => rowBPair (C ω) (τ ω) T (v ω) i) := by
  have hG := measurable_ridgeGram.comp (hC.prodMk hτ)
  have hInv := AndersonAC.AgentS6.measurable_matrix_inv.comp hG
  have hi : Measurable (fun ω => C ω i) := (measurable_pi_apply i).comp hC
  have hb : Measurable (fun ω => ∑ j ∈ T, v ω j • star (C ω j)) := by
    refine Measurable.of_eval fun b => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
    exact Finset.measurable_sum T fun j _ =>
      ((measurable_pi_apply j).comp hv).mul (continuous_star.measurable.comp hC.eval_matrix)
  exact hi.dotProduct' (hInv.mulVec' hb)

lemma measurable_rowPair (x i : R) :
    Measurable (fun p : Matrix R B ℂ × ℝ => rowPair p.1 p.2 x i) := by
  have hG : Measurable (fun p : Matrix R B ℂ × ℝ => ridgeGram p.1 p.2) :=
    (Continuous.add (continuous_fst.matrix_conjTranspose.matrix_mul continuous_fst)
      ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)).measurable
  have hInv := AndersonAC.AgentS6.measurable_matrix_inv.comp hG
  have hx : Measurable (fun p : Matrix R B ℂ × ℝ => p.1 x) :=
    (measurable_pi_apply x).comp measurable_fst
  have hi0 : Measurable (fun p : Matrix R B ℂ × ℝ => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hi : Measurable (fun p : Matrix R B ℂ × ℝ => star (p.1 i)) :=
    continuous_star.measurable.comp hi0
  exact hx.dotProduct' (hInv.mulVec' hi)

lemma norm_rowS_le_m {ι : Type*} (H : NHeat ι B) (i : ι) (hmi : H.lev i ≤ H.m) :
    ‖rowS H i‖ ≤ H.m := by
  have hcs := norm_dotProduct_sq_le H.ux (star (H.u i))
  rw [nsq_star] at hcs
  change ‖rowS H i‖ ^ 2 ≤ H.m * H.lev i at hcs
  have hmul := mul_le_mul_of_nonneg_left hmi H.m_nn
  change H.m * H.lev i ≤ H.m * H.m at hmul
  have hn := norm_nonneg (rowS H i)
  have hm := H.m_nn
  nlinarith

lemma norm_rowB_le {ι : Type*} (H : NHeat ι B) {t c : ℝ} (ht : 0 < t)
    (hc : 0 < c) (i : ι) (hmi : H.lev i ≤ H.m)
    (hb : nsq H.b ≤ H.m / (t * c ^ 2)) :
    ‖H.u i ⬝ᵥ H.b‖ ≤ H.m / (Real.sqrt t * c) := by
  have hroot : Real.sqrt (nsq H.b) ≤ Real.sqrt H.m / (Real.sqrt t * c) := by
    calc
      _ ≤ Real.sqrt (H.m / (t * c ^ 2)) := Real.sqrt_le_sqrt hb
      _ = _ := by
        rw [Real.sqrt_div H.m_nn, Real.sqrt_mul ht.le, Real.sqrt_sq hc.le]
  have hu : Real.sqrt (nsq (H.u i)) ≤ Real.sqrt H.m := Real.sqrt_le_sqrt hmi
  calc
    _ ≤ Real.sqrt (nsq (H.u i)) * Real.sqrt (nsq H.b) := norm_dotProduct_le _ _
    _ ≤ Real.sqrt H.m * (Real.sqrt H.m / (Real.sqrt t * c)) := by gcongr
    _ = _ := by rw [← mul_div_assoc, Real.mul_self_sqrt H.m_nn]


lemma ambient_rowScalars_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (x i : ι) (hxc : x ∉ core) (hic : i ∉ core) (τ : ℝ)
    (L : Matrix core core ℂ) (v : ι → ℂ)
    (hL : L * Lᴴ = (AndersonAC.L64.gram (ambientScattering t r s) core coreᶜ + (τ : ℂ) • 1)⁻¹) :
    rowS (nheat (ambientScattering t r s) L x v) i = rowPair (trialCross t r s) τ x i ∧
    ((nheat (ambientScattering t r s) L x v).u i ⬝ᵥ
      (nheat (ambientScattering t r s) L x v).b) =
        rowBPair (trialCross t r s) τ (coreᶜ.erase x) v i := by
  have hL' : L * Lᴴ = (ridgeGram (trialCross t r s) τ)⁻¹ := by
    simpa only [ridgeGram, ambientGram_eq] using hL
  have hxi := ambientCross_eq t r s i hic
  have hxx := ambientCross_eq t r s x hxc
  constructor
  · change (crossRow (ambientScattering t r s) core x ᵥ* L) ⬝ᵥ
        star (crossRow (ambientScattering t r s) core i ᵥ* L) = _
    rw [hxi, hxx]
    exact normalized_rowPair _ τ L hL' x i
  · change (crossRow (ambientScattering t r s) core i ᵥ* L) ⬝ᵥ
        (∑ a ∈ coreᶜ.erase x, v a • star (crossRow (ambientScattering t r s) core a ᵥ* L)) = _
    have he : (∑ a ∈ coreᶜ.erase x, v a • star (crossRow (ambientScattering t r s) core a ᵥ* L)) =
        ∑ a ∈ coreᶜ.erase x, v a • star (trialCross t r s a ᵥ* L) := by
      exact Finset.sum_congr rfl fun a ha => by
        rw [ambientCross_eq t r s a (Finset.mem_compl.mp (Finset.mem_of_mem_erase ha))]
    rw [hxi, he]
    exact normalized_rowBPair _ τ L hL' _ v i

end AndersonAC.AgentS6Row
