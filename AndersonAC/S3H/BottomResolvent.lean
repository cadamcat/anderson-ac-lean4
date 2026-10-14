import Mathlib
import AndersonAC.S3.HelperStatements
import AndersonAC.S3.HelperStatements2
import AndersonAC.S3.Dispersion

set_option maxHeartbeats 1000000

noncomputable section
open MeasureTheory Set
open Module
open scoped BigOperators NNReal ENNReal Pointwise

namespace AndersonAC.S3

private theorem periodScaleUnit : IsUnit (2 * Real.pi : ℝ) :=
  isUnit_iff_ne_zero.mpr (by positivity : (2 * Real.pi : ℝ) ≠ 0)

private def periodBasis (d : ℕ) : Module.Basis (Fin d) ℝ (Frequency d) :=
  (Pi.basisFun ℝ (Fin d)).isUnitSMul
    (fun _ => periodScaleUnit)

private def periodFundamentalDomain (d : ℕ) : Set (Frequency d) :=
  ZSpan.fundamentalDomain (periodBasis d)

private def periodLattice (d : ℕ) : Submodule ℤ (Frequency d) :=
  Submodule.span ℤ (Set.range (periodBasis d))

private theorem periodFundamentalDomain_eq (d : ℕ) :
    periodFundamentalDomain d = Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) (2 * Real.pi)) := by
  ext x
  simp only [periodFundamentalDomain, ZSpan.fundamentalDomain, Set.mem_ofPred_eq,
    Set.mem_pi, Set.mem_univ, true_implies]
  change (∀ i, (periodBasis d).repr x i ∈ Set.Ico (0 : ℝ) 1) ↔
    ∀ i, x i ∈ Set.Ico (0 : ℝ) (2 * Real.pi)
  have ht : 0 < 2 * Real.pi := by positivity
  have hrepr : ∀ i, (periodBasis d).repr x i = x i / (2 * Real.pi) := by
    intro i
    simp [periodBasis, Basis.repr_isUnitSMul, Pi.basisFun_repr, Units.smul_def,
      Units.val_inv_eq_inv_val]
    all_goals field_simp
  simp only [Set.mem_Ico]
  simp_rw [hrepr]
  constructor
  · intro h j
    have hj := h j
    constructor
    · rcases (div_nonneg_iff.mp hj.1) with ⟨hx, _⟩ | ⟨_, hbad⟩
      · exact hx
      · linarith
    · simpa using (div_lt_iff₀ ht).mp hj.2
  · intro h j
    have hj := h j
    constructor
    · exact div_nonneg hj.1 ht.le
    · exact (div_lt_iff₀ ht).mpr (by simpa using hj.2)

private theorem torusCube_periodFundamentalDomain (d : ℕ) :
    IsAddFundamentalDomain (periodLattice d) (torusCube d) volume := by
  have hbase : IsAddFundamentalDomain (periodLattice d) (periodFundamentalDomain d) volume := by
    exact ZSpan.isAddFundamentalDomain (periodBasis d) volume
  let shift : Frequency d := fun _ => -Real.pi
  have hshift := hbase.vadd_of_comm shift
  have hset : shift +ᵥ periodFundamentalDomain d = torusCube d := by
    rw [periodFundamentalDomain_eq]
    ext k
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_pi, Set.mem_univ, true_implies,
      vadd_eq_add, shift, torusCube, Set.mem_Ico]
    constructor
    · intro h j
      have hj := h j
      simp only [Pi.add_apply, Pi.neg_apply, neg_neg] at hj
      constructor <;> linarith [Real.pi_pos]
    · intro h j
      have hj := h j
      simp only [Pi.add_apply, Pi.neg_apply, neg_neg] at ⊢
      constructor <;> linarith [Real.pi_pos]
  rw [← hset]
  exact hshift

private theorem integral_periodic_phase_shift (d : ℕ) (f : Frequency d → ℂ)
    (φ : Frequency d)
    (hperiod : ∀ g ∈ periodLattice d, ∀ x, f (g + x) = f x) :
    (∫ x in torusCube d, f (x + φ)) = ∫ x in torusCube d, f x := by
  letI : VAddInvariantMeasure (periodLattice d) (Frequency d) volume :=
    ⟨fun g s _ => by
      change volume ((fun x : Frequency d => (g : Frequency d) + x) ⁻¹' s) = volume s
      exact measure_preimage_add volume (g : Frequency d) s⟩
  haveI : Countable (periodLattice d) := by
    dsimp [periodLattice]
    infer_instance
  let hcube := torusCube_periodFundamentalDomain d
  let htranslated := hcube.vadd_of_comm (-φ)
  have hper : ∀ g : periodLattice d, ∀ x,
      (fun x => f (x + φ)) (g +ᵥ x) = (fun x => f (x + φ)) x := by
    intro g x
    change f ((g.1 + x) + φ) = f (x + φ)
    rw [add_assoc]
    exact hperiod g.1 g.2 (x + φ)
  have hfd := hcube.setIntegral_eq htranslated (f := fun x => f (x + φ)) hper
  have hchange :
      (∫ x in (-φ) +ᵥ torusCube d, f (x + φ)) = ∫ x in torusCube d, f x := by
    rw [← image_vadd]
    calc
      (∫ x in ((fun x : Frequency d => -φ + x) '' torusCube d), f (x + φ)) =
          ∫ x in torusCube d, f ((-φ + x) + φ) := by
            exact (measurePreserving_add_left volume (-φ)).setIntegral_image_emb
              (measurableEmbedding_addLeft (-φ)) (fun x => f (x + φ)) (torusCube d)
      _ = ∫ x in torusCube d, f x := by
        congr 1
        funext x
        simp [add_assoc, add_comm (-φ) x]
  exact hfd.trans hchange

private def rayEnergy {d : ℕ} (a ω : Frequency d) (r : ℝ) : ℝ :=
  2 * ∑ j, a j * (1 - Real.cos (r * ω j))

private def rayEnergyDeriv {d : ℕ} (a ω : Frequency d) (r : ℝ) : ℝ :=
  2 * ∑ j, a j * ω j * Real.sin (r * ω j)

private def rayEnergySecond {d : ℕ} (a ω : Frequency d) (r : ℝ) : ℝ :=
  2 * ∑ j, a j * ω j ^ 2 * Real.cos (r * ω j)

private def bottomEnergy {d : ℕ} (a k : Frequency d) : ℝ :=
  2 * ∑ j, a j * (1 - Real.cos (k j))

private theorem rayEnergy_hasDerivAt {d : ℕ} (a ω : Frequency d) (r : ℝ) :
    HasDerivAt (rayEnergy a ω) (rayEnergyDeriv a ω r) r := by
  unfold rayEnergy rayEnergyDeriv
  have hsum : HasDerivAt (fun s : ℝ => ∑ j : Fin d, a j * (1 - Real.cos (s * ω j)))
      (∑ j : Fin d, a j * ω j * Real.sin (r * ω j)) r := by
    apply HasDerivAt.fun_sum
    intro j hj
    have harg : HasDerivAt (fun s : ℝ => s * ω j) (ω j) r := hasDerivAt_mul_const _
    have hcos := harg.cos
    have hsub : HasDerivAt (fun s : ℝ => 1 - Real.cos (s * ω j))
        (Real.sin (r * ω j) * ω j) r := by
      convert (hasDerivAt_one (x := r)).sub hcos using 1 <;> ring
    convert hsub.const_mul (a j) using 1 <;> ring
  convert hsum.const_mul (2 : ℝ) using 1 <;> simp [mul_comm, mul_left_comm, mul_assoc]

private theorem rayEnergyDeriv_hasDerivAt {d : ℕ} (a ω : Frequency d) (r : ℝ) :
    HasDerivAt (rayEnergyDeriv a ω) (rayEnergySecond a ω r) r := by
  unfold rayEnergyDeriv rayEnergySecond
  have hsum : HasDerivAt (fun s : ℝ => ∑ j : Fin d, a j * ω j * Real.sin (s * ω j))
      (∑ j : Fin d, a j * ω j ^ 2 * Real.cos (r * ω j)) r := by
    apply HasDerivAt.fun_sum
    intro j hj
    have harg : HasDerivAt (fun s : ℝ => s * ω j) (ω j) r := hasDerivAt_mul_const _
    convert (harg.sin).const_mul (a j * ω j) using 1 <;> ring
  convert hsum.const_mul (2 : ℝ) using 1 <;> simp [mul_comm, mul_left_comm, mul_assoc]

private theorem unit_coord_sq_le_one {d : ℕ} (ω : Frequency d)
    (hω : ∑ j, ω j ^ 2 = 1) (j : Fin d) : ω j ^ 2 ≤ 1 := by
  have h := Finset.single_le_sum (fun i _ => sq_nonneg (ω i)) (Finset.mem_univ j)
  simpa [hω] using h

private theorem sin_ge_half_mul_of_le (x : ℝ) (hx₀ : 0 ≤ x) (hx : x ≤ 3 / 10) :
    x / 2 ≤ Real.sin x := by
  have hx2 : x ^ 2 ≤ (3 / 10 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (x - 3 / 10)]
  have hcoef : 0 ≤ 1 / 20 - x ^ 2 / 6 := by nlinarith
  have hmul := mul_nonneg hx₀ hcoef
  have hsin := Real.sin_ge_sub_cube hx₀
  nlinarith

private theorem ray_energy_derivative_bounds {d : ℕ} (a ω : Frequency d)
    (ha : ∀ j, 3 / 4 ≤ a j ∧ a j ≤ 5 / 4)
    (hω : ∑ j, ω j ^ 2 = 1) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) (3 / 10)) :
    r / 2 ≤ rayEnergyDeriv a ω r ∧ rayEnergyDeriv a ω r ≤ 3 * r ∧
      |rayEnergySecond a ω r| ≤ 3 := by
  have hcoordAbs (j : Fin d) : |ω j| ≤ 1 := by
    have hs := unit_coord_sq_le_one ω hω j
    rw [abs_le]
    constructor <;> nlinarith [hs]
  have hsinBounds (j : Fin d) :
      (r * |ω j|) / 2 ≤ Real.sin (r * |ω j|) ∧
      Real.sin (r * |ω j|) ≤ r * |ω j| := by
    have harg₀ : 0 ≤ r * |ω j| := mul_nonneg hr.1 (abs_nonneg _)
    have harg : r * |ω j| ≤ 3 / 10 := by
      calc
        r * |ω j| ≤ (3 / 10) * |ω j| := mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)
        _ ≤ 3 / 10 := by nlinarith [hcoordAbs j]
    exact ⟨sin_ge_half_mul_of_le _ harg₀ harg, Real.sin_le harg₀⟩
  have hprodBounds (j : Fin d) :
      r * ω j ^ 2 / 2 ≤ ω j * Real.sin (r * ω j) ∧
      ω j * Real.sin (r * ω j) ≤ r * ω j ^ 2 := by
    let x := r * |ω j|
    have hident : ω j * Real.sin (r * ω j) = |ω j| * Real.sin x := by
      by_cases hsign : 0 ≤ ω j
      · have hx : x = r * ω j := by simp [x, abs_of_nonneg hsign]
        rw [abs_of_nonneg hsign, hx]
      · have hneg : ω j < 0 := lt_of_not_ge hsign
        have hx : x = r * (-ω j) := by simp [x, abs_of_neg hneg]
        have harg : r * ω j = -x := by rw [hx]; ring
        rw [abs_of_neg hneg, harg, Real.sin_neg]
        ring
    have hsin := hsinBounds j
    have habsSq : |ω j| ^ 2 = ω j ^ 2 := sq_abs _
    constructor
    · calc
        r * ω j ^ 2 / 2 = |ω j| * (r * |ω j| / 2) := by rw [← sq_abs]; ring
        _ ≤ |ω j| * Real.sin x := mul_le_mul_of_nonneg_left hsin.1 (abs_nonneg _)
        _ = ω j * Real.sin (r * ω j) := hident.symm
    · calc
        ω j * Real.sin (r * ω j) = |ω j| * Real.sin x := hident
        _ ≤ |ω j| * (r * |ω j|) := mul_le_mul_of_nonneg_left hsin.2 (abs_nonneg _)
        _ = r * ω j ^ 2 := by rw [← sq_abs]; ring
  have htermLow (j : Fin d) :
      (3 / 4 : ℝ) * (r * ω j ^ 2 / 2) ≤ a j * (ω j * Real.sin (r * ω j)) := by
    have hq := hprodBounds j
    have hq0 : 0 ≤ ω j * Real.sin (r * ω j) := by
      have hbase : 0 ≤ r * ω j ^ 2 / 2 :=
        div_nonneg (mul_nonneg hr.1 (sq_nonneg (ω j))) (by norm_num)
      exact hbase.trans hq.1
    calc
      (3 / 4 : ℝ) * (r * ω j ^ 2 / 2) ≤ (3 / 4) * (ω j * Real.sin (r * ω j)) :=
        mul_le_mul_of_nonneg_left hq.1 (by norm_num)
      _ ≤ a j * (ω j * Real.sin (r * ω j)) :=
        mul_le_mul_of_nonneg_right (ha j).1 hq0
  have htermHigh (j : Fin d) :
      a j * (ω j * Real.sin (r * ω j)) ≤ (5 / 4 : ℝ) * (r * ω j ^ 2) := by
    have hq := hprodBounds j
    have hq0 : 0 ≤ ω j * Real.sin (r * ω j) := by
      have hbase : 0 ≤ r * ω j ^ 2 / 2 :=
        div_nonneg (mul_nonneg hr.1 (sq_nonneg (ω j))) (by norm_num)
      exact hbase.trans hq.1
    calc
      a j * (ω j * Real.sin (r * ω j)) ≤ (5 / 4) * (ω j * Real.sin (r * ω j)) :=
        mul_le_mul_of_nonneg_right (ha j).2 hq0
      _ ≤ (5 / 4) * (r * ω j ^ 2) := mul_le_mul_of_nonneg_left hq.2 (by norm_num)
  have hsumLow : (3 / 8 : ℝ) * r ≤ ∑ j, a j * (ω j * Real.sin (r * ω j)) := by
    have hrSum : ∑ j, r * ω j ^ 2 = r := by
      rw [← Finset.mul_sum, hω, mul_one]
    calc
      (3 / 8 : ℝ) * r = (3 / 8) * ∑ j, r * ω j ^ 2 := by rw [hrSum]
      _ = ∑ j, (3 / 8 : ℝ) * (r * ω j ^ 2) := by rw [Finset.mul_sum]
      _ = ∑ j, (3 / 4 : ℝ) * (r * ω j ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j, a j * (ω j * Real.sin (r * ω j)) := Finset.sum_le_sum (fun j _ => htermLow j)
  have hsumHigh : ∑ j, a j * (ω j * Real.sin (r * ω j)) ≤ (5 / 4 : ℝ) * r := by
    have hrSum : ∑ j, r * ω j ^ 2 = r := by
      rw [← Finset.mul_sum, hω, mul_one]
    calc
      ∑ j, a j * (ω j * Real.sin (r * ω j)) ≤ ∑ j, (5 / 4 : ℝ) * (r * ω j ^ 2) :=
        Finset.sum_le_sum (fun j _ => htermHigh j)
      _ = (5 / 4 : ℝ) * ∑ j, r * ω j ^ 2 := by rw [Finset.mul_sum]
      _ = (5 / 4 : ℝ) * r := by rw [hrSum]
  have htermAbs (j : Fin d) :
      |a j * ω j ^ 2 * Real.cos (r * ω j)| ≤ (5 / 4 : ℝ) * ω j ^ 2 := by
    have ha0 : 0 ≤ a j := by linarith [(ha j).1]
    have hfac : 0 ≤ a j * ω j ^ 2 := mul_nonneg ha0 (sq_nonneg _)
    calc
      |a j * ω j ^ 2 * Real.cos (r * ω j)| =
          (a j * ω j ^ 2) * |Real.cos (r * ω j)| := by
            simp only [abs_mul, abs_of_nonneg ha0,
              abs_of_nonneg (sq_nonneg (ω j))]
      _ ≤ (a j * ω j ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hfac
      _ ≤ (5 / 4 : ℝ) * ω j ^ 2 :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_right (ha j).2 (sq_nonneg (ω j))
  have hsec : |rayEnergySecond a ω r| ≤ 5 / 2 := by
    unfold rayEnergySecond
    have htriangle :
        |∑ j : Fin d, a j * ω j ^ 2 * Real.cos (r * ω j)| ≤
          ∑ j : Fin d, |a j * ω j ^ 2 * Real.cos (r * ω j)| := by
      exact Finset.abs_sum_le_sum_abs
        (fun j : Fin d => a j * ω j ^ 2 * Real.cos (r * ω j)) Finset.univ
    have hrSum : ∑ j : Fin d, ω j ^ 2 = 1 := hω
    calc
      |2 * ∑ j, a j * ω j ^ 2 * Real.cos (r * ω j)| =
          2 * |∑ j, a j * ω j ^ 2 * Real.cos (r * ω j)| := by simp
      _ ≤ 2 * ∑ j, |a j * ω j ^ 2 * Real.cos (r * ω j)| :=
        mul_le_mul_of_nonneg_left htriangle (by norm_num)
      _ ≤ 2 * ∑ j, (5 / 4 : ℝ) * ω j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => htermAbs j)) (by norm_num)
      _ = 2 * ((5 / 4 : ℝ) * ∑ j, ω j ^ 2) := by rw [← Finset.mul_sum]
      _ = 5 / 2 := by rw [hrSum]; norm_num
  have hderivRearrange : rayEnergyDeriv a ω r =
      2 * ∑ j, a j * (ω j * Real.sin (r * ω j)) := by
    unfold rayEnergyDeriv
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  constructor
  · rw [hderivRearrange]
    nlinarith [hsumLow]
  constructor
  · rw [hderivRearrange]
    nlinarith [hsumHigh, hr.1]
  · nlinarith [hsec]

private theorem ray_energy_endpoint_gt {d : ℕ} (a ω : Frequency d)
    (ha : ∀ j, 3 / 4 ≤ a j ∧ a j ≤ 5 / 4)
    (hω : ∑ j, ω j ^ 2 = 1) : 1 / 40 < rayEnergy a ω (3 / 10) := by
  have hcoordAbs (j : Fin d) : |ω j| ≤ 1 := by
    have hs := unit_coord_sq_le_one ω hω j
    rw [abs_le]
    constructor <;> nlinarith [hs]
  have hnorm : ∑ j : Fin d, ((3 / 10 : ℝ) * ω j) ^ 2 = 9 / 100 := by
    calc
      ∑ j : Fin d, ((3 / 10 : ℝ) * ω j) ^ 2 =
          (3 / 10 : ℝ) ^ 2 * ∑ j : Fin d, ω j ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = 9 / 100 := by rw [hω]; norm_num
  have hterm (j : Fin d) :
      (3 / 4 : ℝ) * (2 / Real.pi ^ 2) * ((3 / 10 : ℝ) * ω j) ^ 2 ≤
        a j * (1 - Real.cos ((3 / 10 : ℝ) * ω j)) := by
    have hx : |(3 / 10 : ℝ) * ω j| ≤ Real.pi := by
      rw [abs_mul]
      have hpi : (3 / 10 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [hcoordAbs j]
    have hcos := Real.cos_le_one_sub_mul_cos_sq hx
    have hlow : 2 / Real.pi ^ 2 * ((3 / 10 : ℝ) * ω j) ^ 2 ≤
        1 - Real.cos ((3 / 10 : ℝ) * ω j) := by linarith
    have hlow0 : 0 ≤ 2 / Real.pi ^ 2 * ((3 / 10 : ℝ) * ω j) ^ 2 := by positivity
    have ha0 : 0 ≤ a j := by linarith [(ha j).1]
    calc
      (3 / 4 : ℝ) * (2 / Real.pi ^ 2) * ((3 / 10 : ℝ) * ω j) ^ 2 ≤
          a j * (2 / Real.pi ^ 2 * ((3 / 10 : ℝ) * ω j) ^ 2) := by
            calc
              (3 / 4 : ℝ) * (2 / Real.pi ^ 2) * ((3 / 10 : ℝ) * ω j) ^ 2 =
                  (3 / 4 : ℝ) * (2 / Real.pi ^ 2 * ((3 / 10 : ℝ) * ω j) ^ 2) := by ring
              _ ≤ a j * (2 / Real.pi ^ 2 * ((3 / 10 : ℝ) * ω j) ^ 2) :=
                mul_le_mul_of_nonneg_right (ha j).1 hlow0
      _ ≤ a j * (1 - Real.cos ((3 / 10 : ℝ) * ω j)) :=
        mul_le_mul_of_nonneg_left hlow ha0
  have hsumLower : 27 / (200 * Real.pi ^ 2) ≤
      ∑ j : Fin d, a j * (1 - Real.cos ((3 / 10 : ℝ) * ω j)) := by
    calc
      27 / (200 * Real.pi ^ 2) =
          ∑ j : Fin d, (3 / 4 : ℝ) * (2 / Real.pi ^ 2) *
            ((3 / 10 : ℝ) * ω j) ^ 2 := by
              rw [← Finset.mul_sum, hnorm]
              ring
      _ ≤ ∑ j : Fin d, a j * (1 - Real.cos ((3 / 10 : ℝ) * ω j)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
  have henergy : 27 / (100 * Real.pi ^ 2) ≤ rayEnergy a ω (3 / 10) := by
    unfold rayEnergy
    calc
      27 / (100 * Real.pi ^ 2) = 2 * (27 / (200 * Real.pi ^ 2)) := by ring
      _ ≤ 2 * ∑ j : Fin d, a j * (1 - Real.cos ((3 / 10 : ℝ) * ω j)) :=
        mul_le_mul_of_nonneg_left hsumLower (by norm_num)
  have hpi : Real.pi < 315 / 100 := by nlinarith [Real.pi_lt_d2]
  have hpiSq : Real.pi ^ 2 < 10 := by
    have hsquare := (sq_lt_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 315 / 100)).2 hpi
    norm_num at hsquare ⊢
    exact hsquare.trans (by norm_num)
  have htight : 1 / 40 < 27 / (100 * Real.pi ^ 2) := by
    apply (lt_div_iff₀ (by positivity : 0 < 100 * Real.pi ^ 2)).2
    nlinarith [hpiSq]
  exact htight.trans_le henergy

private theorem radius_smul_unit {d : ℕ} (r : ℝ) (ω : Frequency d)
    (hω : ∑ j, ω j ^ 2 = 1) (hr : 0 < r) : radius (r • ω) = r := by
  have hsum : ∑ j : Fin d, (r * ω j) ^ 2 = r ^ 2 := by
    calc
      ∑ j : Fin d, (r * ω j) ^ 2 = r ^ 2 * ∑ j : Fin d, ω j ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = r ^ 2 := by rw [hω]; ring
  unfold radius
  simp [Pi.smul_apply, smul_eq_mul, hsum, Real.sqrt_sq_eq_abs, abs_of_pos hr]

private theorem rayEnergy_eq_dispersion {d : ℕ} (ω : Frequency d) (r : ℝ) :
    rayEnergy (fun _ : Fin d => (1 : ℝ)) ω r = dispersion (r • ω) + 2 * (d : ℝ) := by
  unfold rayEnergy dispersion
  simp [Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Fintype.card_fin, nsmul_eq_mul]
  ring_nf

private theorem bottomEnergy_one_eq_dispersion {d : ℕ} (k : Frequency d) :
    bottomEnergy (fun _ : Fin d => (1 : ℝ)) k = dispersion k + 2 * (d : ℝ) := by
  unfold bottomEnergy dispersion
  simp [Finset.sum_sub_distrib, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  ring_nf

private theorem bottomEnergy_free_lower {d : ℕ} (k : Frequency d)
    (hk : ∀ j, |k j| ≤ Real.pi) :
    (4 / Real.pi ^ 2) * radius k ^ 2 ≤ bottomEnergy (fun _ : Fin d => (1 : ℝ)) k := by
  have hcoord (j : Fin d) :
      (4 / Real.pi ^ 2) * k j ^ 2 ≤ 4 * Real.sin (k j / 2) ^ 2 := by
    have hx : |k j / 2| ≤ Real.pi / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := hk j
      nlinarith [Real.pi_pos]
    have hsin := Real.mul_abs_le_abs_sin hx
    have hsq := (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 hsin
    have hcalc : (2 / Real.pi * |k j / 2|) ^ 2 =
        (1 / Real.pi ^ 2) * k j ^ 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        (2 / Real.pi * (|k j| / 2)) ^ 2 = (1 / Real.pi ^ 2) * |k j| ^ 2 := by ring
        _ = (1 / Real.pi ^ 2) * k j ^ 2 := by rw [sq_abs]
    rw [hcalc, sq_abs] at hsq
    calc
      (4 / Real.pi ^ 2) * k j ^ 2 = 4 * ((1 / Real.pi ^ 2) * k j ^ 2) := by ring
      _ ≤ 4 * Real.sin (k j / 2) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hrad2 : radius k ^ 2 = ∑ j, k j ^ 2 := by
    unfold radius
    exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (k j))
  have hsum : (4 / Real.pi ^ 2) * radius k ^ 2 ≤ laplacianSymbol k := by
    rw [hrad2]
    unfold laplacianSymbol
    calc
      (4 / Real.pi ^ 2) * ∑ j, k j ^ 2 =
          ∑ j, (4 / Real.pi ^ 2) * k j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ j, 4 * Real.sin (k j / 2) ^ 2 := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = 4 * ∑ j, Real.sin (k j / 2) ^ 2 := by rw [Finset.mul_sum]
  have hbottom : bottomEnergy (fun _ : Fin d => (1 : ℝ)) k = laplacianSymbol k := by
    rw [bottomEnergy_one_eq_dispersion, dispersion_identity_proof]
    ring
  simpa [hbottom] using hsum

private def amplitudeExcess {d : ℕ} (a : Frequency d) : ℝ :=
  2 * ∑ j, (a j - 1)

private theorem bottomEnergy_eq_perturbed {d : ℕ} (a k : Frequency d) :
    bottomEnergy a k + 2 * ∑ j, (1 - a j) =
      perturbedDispersion a 0 k + 2 * (d : ℝ) := by
  have hcos : (∑ j : Fin d, a j * (1 - Real.cos (k j))) =
      (∑ j : Fin d, a j) - ∑ j : Fin d, a j * Real.cos (k j) := by
    calc
      ∑ j : Fin d, a j * (1 - Real.cos (k j)) =
          ∑ j : Fin d, (a j - a j * Real.cos (k j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j : Fin d, a j) - ∑ j : Fin d, a j * Real.cos (k j) :=
        by rw [Finset.sum_sub_distrib]
  have hshift : (∑ j : Fin d, (1 - a j)) =
      (d : ℝ) - ∑ j : Fin d, a j := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  unfold bottomEnergy perturbedDispersion
  simp only [Pi.zero_apply, add_zero]
  rw [hcos, hshift]
  ring_nf

private theorem rayEnergy_eq_perturbed {d : ℕ} (a ω : Frequency d) (r : ℝ) :
    rayEnergy a ω r + 2 * ∑ j, (1 - a j) =
      perturbedDispersion a 0 (r • ω) + 2 * (d : ℝ) := by
  have h := bottomEnergy_eq_perturbed a (r • ω)
  simpa [bottomEnergy, rayEnergy, Pi.smul_apply, smul_eq_mul] using h

private theorem amplitudeShift_identity {d : ℕ} (a : Frequency d) :
    2 * ∑ j, (1 - a j) = -amplitudeExcess a := by
  have hsum : ∑ j : Fin d, (1 - a j) = -∑ j : Fin d, (a j - 1) := by
    calc
      ∑ j : Fin d, (1 - a j) = ∑ j : Fin d, (-(a j - 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -∑ j : Fin d, (a j - 1) := by rw [Finset.sum_neg_distrib]
  unfold amplitudeExcess
  rw [hsum]
  ring

private theorem rayEnergy_perturbed_denominator {d : ℕ} (a ω : Frequency d)
    (β r : ℝ) :
    perturbedDispersion a 0 (r • ω) + 2 * (d : ℝ) - β =
      rayEnergy a ω r - (β + amplitudeExcess a) := by
  have hid := rayEnergy_eq_perturbed a ω r
  have hshift := amplitudeShift_identity a
  linarith

private theorem rayEnergy_free_denominator {d : ℕ} (ω : Frequency d) (β r : ℝ) :
    dispersion (r • ω) + 2 * (d : ℝ) - β =
      rayEnergy (fun _ : Fin d => (1 : ℝ)) ω r - β := by
  rw [← rayEnergy_eq_dispersion]

private theorem periodBasis_coord {d : ℕ} (i j : Fin d) :
    periodBasis d i j = if j = i then 2 * Real.pi else 0 := by
  simp [periodBasis, Basis.isUnitSMul_apply, Pi.basisFun_apply, Pi.single_apply,
    Units.smul_def, periodScaleUnit]

private def radiusBall (d : ℕ) (ρ : ℝ) : Set (Frequency d) :=
  {k | radius k ≤ ρ}

private def radiusBox (d : ℕ) (ρ : ℝ) : Set (Frequency d) :=
  Set.pi Set.univ (fun _ : Fin d => Set.Icc (-ρ) ρ)

private theorem radius_coord_le {d : ℕ} (k : Frequency d) (j : Fin d) :
    |k j| ≤ radius k := by
  have hsum0 : 0 ≤ ∑ i : Fin d, k i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (k i)
  have hsumj : k j ^ 2 ≤ ∑ i : Fin d, k i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (k i)) (Finset.mem_univ j)
  have hrad2 : radius k ^ 2 = ∑ i : Fin d, k i ^ 2 := by
    unfold radius
    exact Real.sq_sqrt hsum0
  unfold radius at hrad2
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [hrad2]
  simpa only [sq_abs] using hsumj

private theorem radiusBall_subset_box {d : ℕ} (ρ : ℝ) :
    radiusBall d ρ ⊆ radiusBox d ρ := by
  intro k hk
  change radius k ≤ ρ at hk
  simp only [radiusBox, Set.mem_pi, Set.mem_univ, true_implies]
  intro j
  rw [Set.mem_Icc]
  exact abs_le.mp ((radius_coord_le k j).trans hk)

private theorem radiusBall_subset_torusCube (d : ℕ) :
    radiusBall d (3 / 10) ⊆ torusCube d := by
  intro k hk
  change radius k ≤ 3 / 10 at hk
  simp only [torusCube, Set.mem_pi, Set.mem_univ, true_implies]
  intro j
  rw [Set.mem_Ico]
  have habs : |k j| ≤ 3 / 10 := (radius_coord_le k j).trans hk
  have hkabs := abs_le.mp habs
  exact ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

private theorem radiusBox_volume_lt_top (d : ℕ) (ρ : ℝ) :
    volume (radiusBox d ρ) < ∞ := by
  rw [radiusBox, pi_univ_Icc, Real.volume_Icc_pi]
  simp

private theorem radiusBall_volume_lt_top (d : ℕ) (ρ : ℝ) :
    volume (radiusBall d ρ) < ∞ := by
  exact (measure_mono (radiusBall_subset_box (d := d) ρ)).trans_lt (radiusBox_volume_lt_top d ρ)

private theorem measurableSet_radiusBall (d : ℕ) (ρ : ℝ) :
    MeasurableSet (radiusBall d ρ) := by
  have hrad : Measurable (radius : Frequency d → ℝ) := by fun_prop [radius]
  exact measurableSet_le hrad measurable_const

private theorem integrable_indicator_radiusBall {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {ρ M : ℝ} (q : Frequency d → E)
    (hq : AEStronglyMeasurable q volume) (hbound : ∀ k, ‖q k‖ ≤ M) :
    Integrable (Set.indicator (radiusBall d ρ) q) volume := by
  have hOn : IntegrableOn q (radiusBall d ρ) volume :=
    Measure.integrableOn_of_bounded (lt_top_iff_ne_top.mp (radiusBall_volume_lt_top d ρ))
      hq (Filter.Eventually.of_forall hbound)
  exact hOn.integrable_indicator (measurableSet_radiusBall d ρ)

private theorem resolvent_denominator_ne (x β v : ℝ) (hv : 0 < v) :
    ((x : ℂ) - β - v * Complex.I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

private theorem norm_resolvent_le (x β v : ℝ) (hv : 0 < v) :
    ‖(((x : ℂ) - β - v * Complex.I)⁻¹)‖ ≤ v⁻¹ := by
  have hden : ((x : ℂ) - β - v * Complex.I) ≠ 0 := resolvent_denominator_ne x β v hv
  have him : (((x : ℂ) - β - v * Complex.I).im) = -v := by simp
  have hnorm : v ≤ ‖(x : ℂ) - β - v * Complex.I‖ := by
    calc
      v = |((x : ℂ) - β - v * Complex.I).im| := by rw [him]; simp [abs_of_pos hv]
      _ ≤ ‖(x : ℂ) - β - v * Complex.I‖ := Complex.abs_im_le_norm _
  rw [norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hv hnorm

private theorem continuous_resolvent_of_continuous_energy {d : ℕ}
    (E : Frequency d → ℝ) (hE : Continuous E) (β v : ℝ) (hv : 0 < v) :
    Continuous (fun k => (((E k - β : ℝ) : ℂ) - v * Complex.I)⁻¹) := by
  have hden : Continuous (fun k => (((E k - β : ℝ) : ℂ) - v * Complex.I)) := by fun_prop
  apply hden.inv₀
  intro k
  simpa only [Complex.ofReal_sub] using resolvent_denominator_ne (E k) β v hv

private theorem continuous_resolvent_square_of_continuous_energy {d : ℕ}
    (E : Frequency d → ℝ) (hE : Continuous E) (β v : ℝ) (hv : 0 < v) :
    Continuous (fun k => ((((E k - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2) := by
  exact (continuous_resolvent_of_continuous_energy E hE β v hv).pow 2

private theorem continuous_imaginary_resolvent_of_continuous_energy {d : ℕ}
    (E : Frequency d → ℝ) (hE : Continuous E) (β v : ℝ) (hv : 0 < v) :
    Continuous (fun k => v / ((E k - β) ^ 2 + v ^ 2)) := by
  have hden : Continuous (fun k => (E k - β) ^ 2 + v ^ 2) := by fun_prop
  apply continuous_const.div hden
  intro k
  positivity

private theorem imaginary_resolvent_nonneg (x β v : ℝ) (hv : 0 < v) :
    0 ≤ v / ((x - β) ^ 2 + v ^ 2) := by
  exact div_nonneg hv.le (by positivity)

private theorem imaginary_resolvent_le (x β v : ℝ) (hv : 0 < v) :
    v / ((x - β) ^ 2 + v ^ 2) ≤ v⁻¹ := by
  have hden : v ^ 2 ≤ (x - β) ^ 2 + v ^ 2 := by nlinarith [sq_nonneg (x - β)]
  have hmul := mul_le_mul_of_nonneg_left hden (inv_nonneg.mpr hv.le)
  have hleft : v⁻¹ * v ^ 2 = v := by field_simp
  apply (div_le_iff₀ (by positivity : 0 < (x - β) ^ 2 + v ^ 2)).2
  nlinarith [hmul, hleft]

private def freeEnergy {d : ℕ} (k : Frequency d) : ℝ :=
  dispersion k + 2 * (d : ℝ)

private def freeResolvent {d : ℕ} (β v : ℝ) (k : Frequency d) : ℂ :=
  (((freeEnergy k - β : ℝ) : ℂ) - v * Complex.I)⁻¹

private def freeResolventSquare {d : ℕ} (β v : ℝ) (k : Frequency d) : ℂ :=
  freeResolvent β v k ^ 2

private def freeResolventAbs {d : ℕ} (β v : ℝ) (k : Frequency d) : ℝ :=
  ‖freeResolvent β v k‖

private def freeImaginaryDensity {d : ℕ} (β v : ℝ) (k : Frequency d) : ℝ :=
  v / ((freeEnergy k - β) ^ 2 + v ^ 2)

private theorem freeResolvent_eq_ray {d : ℕ} (β v : ℝ) (ω : Frequency d) (r : ℝ) :
    freeResolvent β v (r • ω) =
      (((rayEnergy (fun _ : Fin d => (1 : ℝ)) ω r : ℝ) : ℂ) - β - v * Complex.I)⁻¹ := by
  unfold freeResolvent freeEnergy
  rw [rayEnergy_free_denominator]
  simp only [Complex.ofReal_sub]

private theorem freeImaginaryDensity_eq_ray {d : ℕ} (β v : ℝ) (ω : Frequency d) (r : ℝ) :
    freeImaginaryDensity β v (r • ω) =
      v / ((rayEnergy (fun _ : Fin d => (1 : ℝ)) ω r - β) ^ 2 + v ^ 2) := by
  unfold freeImaginaryDensity freeEnergy
  rw [rayEnergy_free_denominator]

private theorem freeEnergy_continuous {d : ℕ} : Continuous (freeEnergy (d := d)) := by
  unfold freeEnergy dispersion
  fun_prop

private theorem freeResolvent_continuous {d : ℕ} (β v : ℝ) (hv : 0 < v) :
    Continuous (freeResolvent (d := d) β v) := by
  exact continuous_resolvent_of_continuous_energy (freeEnergy (d := d))
    freeEnergy_continuous β v hv

private theorem freeResolventSquare_continuous {d : ℕ} (β v : ℝ) (hv : 0 < v) :
    Continuous (freeResolventSquare (d := d) β v) := by
  exact continuous_resolvent_square_of_continuous_energy (freeEnergy (d := d))
    freeEnergy_continuous β v hv

private theorem freeResolventAbs_continuous {d : ℕ} (β v : ℝ) (hv : 0 < v) :
    Continuous (freeResolventAbs (d := d) β v) :=
  (freeResolvent_continuous β v hv).norm

private theorem freeImaginaryDensity_continuous {d : ℕ} (β v : ℝ) (hv : 0 < v) :
    Continuous (freeImaginaryDensity (d := d) β v) := by
  exact continuous_imaginary_resolvent_of_continuous_energy (freeEnergy (d := d))
    freeEnergy_continuous β v hv

private theorem freeResolvent_norm_bound {d : ℕ} (β v : ℝ) (hv : 0 < v)
    (k : Frequency d) : ‖freeResolvent β v k‖ ≤ v⁻¹ :=
  by
    change ‖(((freeEnergy k - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖ ≤ v⁻¹
    simpa only [Complex.ofReal_sub] using norm_resolvent_le (freeEnergy k) β v hv

private theorem freeResolventSquare_norm_bound {d : ℕ} (β v : ℝ) (hv : 0 < v)
    (k : Frequency d) : ‖freeResolventSquare β v k‖ ≤ (v⁻¹) ^ 2 := by
  have h := freeResolvent_norm_bound β v hv k
  change ‖freeResolvent β v k ^ 2‖ ≤ (v⁻¹) ^ 2
  rw [norm_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr hv.le)).2 h

private theorem freeImaginaryDensity_nonneg {d : ℕ} (β v : ℝ) (hv : 0 < v)
    (k : Frequency d) : 0 ≤ freeImaginaryDensity β v k := by
  exact imaginary_resolvent_nonneg (freeEnergy k) β v hv

private theorem freeImaginaryDensity_bound {d : ℕ} (β v : ℝ) (hv : 0 < v)
    (k : Frequency d) : freeImaginaryDensity β v k ≤ v⁻¹ := by
  exact imaginary_resolvent_le (freeEnergy k) β v hv

private theorem torusCube_measurableSet (d : ℕ) : MeasurableSet (torusCube d) := by
  unfold torusCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

private theorem torusCube_volume_ne_top (d : ℕ) : volume (torusCube d) ≠ ∞ := by
  unfold torusCube
  rw [Real.volume_pi_Ico]
  simp

private theorem integrableOn_of_bounded_on_torusCube {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Frequency d → E) (hf : AEStronglyMeasurable f volume)
    (M : ℝ) (hbound : ∀ k, ‖f k‖ ≤ M) : IntegrableOn f (torusCube d) volume := by
  exact Measure.integrableOn_of_bounded (torusCube_volume_ne_top d)
    hf (Filter.Eventually.of_forall hbound)

private theorem integral_torusCube_split {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Frequency d → E)
    (hCube : IntegrableOn f (torusCube d) volume)
    (hBall : IntegrableOn f (radiusBall d (3 / 10)) volume) :
    (∫ k in torusCube d, f k) =
      (∫ k in radiusBall d (3 / 10), f k) +
        ∫ k in torusCube d \ radiusBall d (3 / 10), f k := by
  have hballSub : radiusBall d (3 / 10) ⊆ torusCube d := radiusBall_subset_torusCube d
  have hunion : radiusBall d (3 / 10) ∪ (torusCube d \ radiusBall d (3 / 10)) = torusCube d := by
    ext k
    by_cases hk : k ∈ radiusBall d (3 / 10)
    · simp [hk, hballSub hk]
    · simp [hk]
  calc
    (∫ k in torusCube d, f k) =
        ∫ k in radiusBall d (3 / 10) ∪ (torusCube d \ radiusBall d (3 / 10)), f k := by
          conv_lhs => rw [← hunion]
    _ = (∫ k in radiusBall d (3 / 10), f k) +
        ∫ k in torusCube d \ radiusBall d (3 / 10), f k :=
      setIntegral_union disjoint_sdiff_self_right
        ((torusCube_measurableSet d).diff (measurableSet_radiusBall d (3 / 10))) hBall
        (hCube.mono_set Set.sdiff_subset)

private theorem norm_integral_torusCube_remainder_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Frequency d → E) (A : ℝ)
    (hvol : volume (torusCube d) ≠ ∞) (hA : 0 ≤ A)
    (hbound : ∀ k ∈ torusCube d \ radiusBall d (3 / 10), ‖f k‖ ≤ A) :
    ‖∫ k in torusCube d \ radiusBall d (3 / 10), f k‖ ≤
      A * volume.real (torusCube d) := by
  have hfinite : volume (torusCube d \ radiusBall d (3 / 10)) < ∞ :=
    (measure_mono Set.sdiff_subset).trans_lt (lt_top_iff_ne_top.mpr hvol)
  calc
    ‖∫ k in torusCube d \ radiusBall d (3 / 10), f k‖ ≤
        A * volume.real (torusCube d \ radiusBall d (3 / 10)) :=
      norm_setIntegral_le_of_norm_le_const hfinite hbound
    _ ≤ A * volume.real (torusCube d) :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono Set.sdiff_subset hvol) hA

private theorem integral_nonneg_torusCube_remainder_le {d : ℕ} (f : Frequency d → ℝ)
    (A : ℝ) (hvol : volume (torusCube d) ≠ ∞) (hA : 0 ≤ A)
    (hnonneg : ∀ k ∈ torusCube d \ radiusBall d (3 / 10), 0 ≤ f k)
    (hbound : ∀ k ∈ torusCube d \ radiusBall d (3 / 10), f k ≤ A) :
    ∫ k in torusCube d \ radiusBall d (3 / 10), f k ≤ A * volume.real (torusCube d) := by
  have hnorm := norm_integral_torusCube_remainder_le f A hvol hA (fun k hk => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg k hk)]
    exact hbound k hk)
  have hI0 : 0 ≤ ∫ k in torusCube d \ radiusBall d (3 / 10), f k :=
    setIntegral_nonneg_of_ae_restrict
      ((ae_restrict_iff' ((torusCube_measurableSet d).diff
        (measurableSet_radiusBall d (3 / 10)))).2
        (Filter.Eventually.of_forall fun k hk => hnonneg k hk))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hI0] using hnorm

private theorem norm_integral_complex_ofReal_of_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ‖∫ x, (f x : ℂ) ∂μ‖ = ∫ x, f x ∂μ := by
  rw [integral_complex_ofReal]
  simp [Complex.norm_real, abs_of_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall hf))]

private theorem norm_interval_integral_complex_ofReal_of_nonneg {f : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : ∀ r ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f r) :
    ‖∫ r in (0 : ℝ)..ρ, (f r : ℂ)‖ = ∫ r in (0 : ℝ)..ρ, f r := by
  have hcast : (∫ r in (0 : ℝ)..ρ, (f r : ℂ)) =
      ((∫ r in (0 : ℝ)..ρ, f r : ℝ) : ℂ) := RCLike.intervalIntegral_ofReal
  rw [hcast]
  simp [Complex.norm_real,
    abs_of_nonneg (intervalIntegral.integral_nonneg hρ fun r hr => hf r hr)]

private theorem amplitudeExcess_abs_le {d : ℕ} (a : Frequency d) (ε : ℝ)
    (hε : ∀ j, |a j - 1| ≤ ε) (hε0 : 0 ≤ ε) :
    |amplitudeExcess a| ≤ 2 * (d : ℝ) * ε := by
  have hsum : ∑ j : Fin d, |a j - 1| ≤ (d : ℝ) * ε := by
    calc
      ∑ j : Fin d, |a j - 1| ≤ ∑ j : Fin d, ε :=
        Finset.sum_le_sum (fun j _ => hε j)
      _ = (d : ℝ) * ε := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  unfold amplitudeExcess
  calc
    |2 * ∑ j, (a j - 1)| = 2 * |∑ j, (a j - 1)| := by simp
    _ ≤ 2 * ∑ j, |a j - 1| :=
      mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs (fun j : Fin d => a j - 1) Finset.univ) (by norm_num)
    _ ≤ 2 * ((d : ℝ) * ε) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * (d : ℝ) * ε := by ring

private theorem amplitude_close_bounds {d : ℕ} (a : Frequency d) (ε : ℝ)
    (hε : ε ≤ 1 / 4) (ha : ∀ j, |a j - 1| ≤ ε) :
    ∀ j, 3 / 4 ≤ a j ∧ a j ≤ 5 / 4 := by
  intro j
  have hj := abs_le.mp (ha j)
  constructor <;> nlinarith

private theorem ray_core_estimates_of_helpers (d : ℕ) (hd : 3 ≤ d)
    (βlo βhi μ : ℝ) (hβlo : 0 < βlo) (hβ : βlo ≤ βhi)
    (hμ : 0 < μ) (hend : βhi + μ ≤ 1 / 40)
    (hRay : RayEstimatesStatement) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a ω : Frequency d, (∀ j, 3 / 4 ≤ a j ∧ a j ≤ 5 / 4) →
        (∑ j, ω j ^ 2 = 1) → ∀ β ∈ Set.Icc βlo βhi, ∀ v : ℝ, 0 < v → v ≤ 1 →
          ‖∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
            (((rayEnergy a ω r : ℂ) - β - v * Complex.I)⁻¹) ^ 2‖ ≤ C * Real.log (2 / v) ∧
          (∫ r in (0 : ℝ)..(3 / 10), r ^ (d - 1) *
            ‖((rayEnergy a ω r : ℂ) - β - v * Complex.I)⁻¹‖) ≤ C * Real.log (2 / v) ∧
          ‖∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
            ((rayEnergy a ω r : ℂ) - β - v * Complex.I)⁻¹‖ ≤ C ∧
          c ≤ ∫ r in (0 : ℝ)..(3 / 10), r ^ (d - 1) *
            (v / ((rayEnergy a ω r - β) ^ 2 + v ^ 2)) := by
  obtain ⟨C, c, hC, hc, hray⟩ := hRay (d - 1) (by omega)
    (1 / 2) 3 (3 / 10) (3 / 10) βlo βhi μ (by norm_num) (by norm_num)
    (by norm_num) hβlo hβ hμ
  refine ⟨C, c, hC, hc, ?_⟩
  intro a ω ha hω β hβmem v hv hv1
  have hderiv : ∀ r ∈ Set.Icc (0 : ℝ) (3 / 10),
      HasDerivAt (rayEnergy a ω) (rayEnergyDeriv a ω r) r ∧
      HasDerivAt (rayEnergyDeriv a ω) (rayEnergySecond a ω r) r ∧
      (1 / 2) * r ≤ rayEnergyDeriv a ω r ∧ rayEnergyDeriv a ω r ≤ 3 * r ∧
      |rayEnergySecond a ω r| ≤ 3 := by
    intro r hr
    have hb := ray_energy_derivative_bounds a ω ha hω r hr
    have hlower : (1 / 2 : ℝ) * r ≤ rayEnergyDeriv a ω r := by nlinarith [hb.1]
    exact ⟨rayEnergy_hasDerivAt a ω r, rayEnergyDeriv_hasDerivAt a ω r,
      hlower, hb.2.1, hb.2.2⟩
  have hzero : rayEnergy a ω 0 = 0 := by simp [rayEnergy]
  have hendRay : βhi + μ ≤ rayEnergy a ω (3 / 10) :=
    hend.trans (le_of_lt (ray_energy_endpoint_gt a ω ha hω))
  exact hray (rayEnergy a ω) (rayEnergyDeriv a ω) (rayEnergySecond a ω) (3 / 10)
    (by norm_num) (by norm_num) hzero hderiv hendRay β hβmem v hv hv1

private theorem perturbed_energy_periodic_basis {d : ℕ} (a : Frequency d) (i : Fin d) :
    Function.Periodic (perturbedDispersion a (0 : Frequency d)) (periodBasis d i) := by
  intro k
  simp only [perturbedDispersion, Pi.add_apply, Pi.zero_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [periodBasis_coord]
  by_cases hji : j = i
  · simp [hji, Real.cos_add_two_pi]
  · simp [hji]

private theorem periodic_on_periodLattice {d : ℕ} (f : Frequency d → ℂ)
    (hbase : ∀ i, Function.Periodic f (periodBasis d i)) :
    ∀ g ∈ periodLattice d, Function.Periodic f g := by
  intro g hg
  unfold periodLattice at hg
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    exact hbase i
  · intro x
    simp [Function.Periodic]
  · intro x y _ _ hx hy
    exact Function.Periodic.add_period hx hy
  · intro z x _ hx
    exact hx.zsmul z

private def perturbedSquareKernel {d : ℕ} (a : Frequency d) (β v : ℝ)
    (k : Frequency d) : ℂ :=
  ((((perturbedDispersion a 0 k + 2 * (d : ℝ) - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2

private theorem perturbedSquareKernel_periodic_basis {d : ℕ} (a : Frequency d)
    (β v : ℝ) (i : Fin d) :
    Function.Periodic (perturbedSquareKernel a β v) (periodBasis d i) := by
  let g : ℝ → ℂ := fun x => ((((x + 2 * (d : ℝ) - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2
  have h := (perturbed_energy_periodic_basis a i).comp g
  change Function.Periodic (g ∘ perturbedDispersion a 0) (periodBasis d i)
  exact h

private theorem perturbedSquareKernel_periodic_lattice {d : ℕ} (a : Frequency d)
    (β v : ℝ) (g : Frequency d) (hg : g ∈ periodLattice d) :
    ∀ k, perturbedSquareKernel a β v (g + k) = perturbedSquareKernel a β v k := by
  intro k
  have h := periodic_on_periodLattice (perturbedSquareKernel a β v)
    (perturbedSquareKernel_periodic_basis a β v) g hg
  simpa [Function.Periodic, add_comm] using h k

private theorem ray_cut_interval_complex {ρ : ℝ} (hρ : 0 ≤ ρ) (g : ℝ → ℂ) :
    (∫ r in Set.Ioi (0 : ℝ), Set.indicator (Set.Iic ρ) g r) = ∫ r in (0 : ℝ)..ρ, g r := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iic ρ = Set.Ioc 0 ρ := by
    ext r
    simp [Set.mem_Ioi, Set.mem_Iic, Set.mem_Ioc]
  rw [hset, intervalIntegral.integral_of_le hρ]

private theorem ray_cut_interval_real {ρ : ℝ} (hρ : 0 ≤ ρ) (g : ℝ → ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), Set.indicator (Set.Iic ρ) g r) = ∫ r in (0 : ℝ)..ρ, g r := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iic ρ = Set.Ioc 0 ρ := by
    ext r
    simp [Set.mem_Ioi, Set.mem_Iic, Set.mem_Ioc]
  rw [hset, intervalIntegral.integral_of_le hρ]

private theorem polar_upper_radiusBall {d : ℕ} (σ M ρ : ℝ)
    (hupper : ∀ f : Frequency d → ℂ, ∀ M : ℝ, Integrable f →
      (∀ ω, (∑ j, ω j ^ 2 = 1) →
        ‖∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * f (r • ω)‖ ≤ M) →
      ‖∫ k, f k‖ ≤ σ * M)
    (hρ : 0 ≤ ρ) (q : Frequency d → ℂ)
    (hq : Integrable (Set.indicator (radiusBall d ρ) q))
    (hray : ∀ ω, (∑ j, ω j ^ 2 = 1) →
      ‖∫ r in (0 : ℝ)..ρ, ((r ^ (d - 1) : ℝ) : ℂ) * q (r • ω)‖ ≤ M) :
    ‖∫ k, Set.indicator (radiusBall d ρ) q k‖ ≤ σ * M := by
  apply hupper (Set.indicator (radiusBall d ρ) q) M hq
  intro ω hω
  calc
    ‖∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) *
        Set.indicator (radiusBall d ρ) q (r • ω)‖ =
      ‖∫ r in Set.Ioi (0 : ℝ), Set.indicator (Set.Iic ρ)
          (fun r => ((r ^ (d - 1) : ℝ) : ℂ) * q (r • ω)) r‖ := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hrpos : 0 < r := hr
        by_cases hrρ : r ≤ ρ <;>
          simp [radiusBall, radius_smul_unit r ω hω hrpos, hrρ]
    _ = ‖∫ r in (0 : ℝ)..ρ, ((r ^ (d - 1) : ℝ) : ℂ) * q (r • ω)‖ := by
      rw [ray_cut_interval_complex hρ]
    _ ≤ M := hray ω hω

private theorem polar_lower_radiusBall {d : ℕ} (σ M ρ : ℝ)
    (hlower : ∀ f : Frequency d → ℝ, ∀ M : ℝ, Integrable f → (∀ k, 0 ≤ f k) →
      (∀ ω, (∑ j, ω j ^ 2 = 1) →
        M ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * f (r • ω)) →
      σ * M ≤ ∫ k, f k)
    (hρ : 0 ≤ ρ) (q : Frequency d → ℝ)
    (hq : Integrable (Set.indicator (radiusBall d ρ) q)) (hq0 : ∀ k, 0 ≤ q k)
    (hray : ∀ ω, (∑ j, ω j ^ 2 = 1) →
      M ≤ ∫ r in (0 : ℝ)..ρ, r ^ (d - 1) * q (r • ω)) :
    σ * M ≤ ∫ k, Set.indicator (radiusBall d ρ) q k := by
  apply hlower (Set.indicator (radiusBall d ρ) q) M hq
  · intro k
    by_cases hk : k ∈ radiusBall d ρ
    · simpa [Set.indicator_of_mem hk] using hq0 k
    · simp [Set.indicator_of_notMem hk]
  · intro ω hω
    calc
      M ≤ ∫ r in (0 : ℝ)..ρ, r ^ (d - 1) * q (r • ω) := hray ω hω
      _ = ∫ r in Set.Ioi (0 : ℝ), Set.indicator (Set.Iic ρ)
          (fun r => r ^ (d - 1) * q (r • ω)) r := by
            rw [ray_cut_interval_real hρ]
      _ = ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) *
          Set.indicator (radiusBall d ρ) q (r • ω) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro r hr
            have hrpos : 0 < r := hr
            by_cases hrρ : r ≤ ρ <;>
              simp [radiusBall, radius_smul_unit r ω hω hrpos, hrρ]

private theorem integrableOn_of_bounded_on_radiusBall {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (ρ : ℝ) (q : Frequency d → E)
    (hq : AEStronglyMeasurable q volume) (M : ℝ) (hbound : ∀ k, ‖q k‖ ≤ M) :
    IntegrableOn q (radiusBall d ρ) volume :=
  Measure.integrableOn_of_bounded
    (lt_top_iff_ne_top.mp (radiusBall_volume_lt_top d ρ)) hq
    (Filter.Eventually.of_forall hbound)

private theorem free_energy_gap_outside_ball {d : ℕ} (k : Frequency d)
    (hk : k ∈ torusCube d) (hout : k ∉ radiusBall d (3 / 10))
    (β : ℝ) (hβ : β ≤ 1 / 50) :
    1 / 100 ≤ freeEnergy k - β := by
  have hcoord : ∀ j, |k j| ≤ Real.pi := by
    intro j
    have hj := hk j
    simp only [torusCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hj
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  have hbottom := bottomEnergy_free_lower k hcoord
  have hpiSq : Real.pi ^ 2 < 10 := by
    have hpi : Real.pi < (63 / 20 : ℝ) := by
      convert Real.pi_lt_d2 using 1 <;> norm_num
    have hsq := (sq_lt_sq₀ (le_of_lt Real.pi_pos) (by norm_num : 0 ≤ (63 / 20 : ℝ))).2 hpi
    nlinarith
  have hcoef : (2 / 5 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith
  have hout' : ¬ radius k ≤ 3 / 10 := by
    simpa [radiusBall] using hout
  have hr : 3 / 10 < radius k := lt_of_not_ge hout'
  have hr2 : (3 / 10 : ℝ) ^ 2 < radius k ^ 2 := by
    nlinarith [sq_nonneg (radius k - 3 / 10)]
  have henergy : (9 / 250 : ℝ) ≤ bottomEnergy (fun _ : Fin d => (1 : ℝ)) k := by
    calc
      9 / 250 = (2 / 5 : ℝ) * (3 / 10) ^ 2 := by norm_num
      _ ≤ (2 / 5 : ℝ) * radius k ^ 2 :=
        mul_le_mul_of_nonneg_left hr2.le (by norm_num)
      _ ≤ (4 / Real.pi ^ 2) * radius k ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ bottomEnergy (fun _ : Fin d => (1 : ℝ)) k := hbottom
  rw [freeEnergy, ← bottomEnergy_one_eq_dispersion]
  nlinarith

private theorem perturbed_energy_gap_outside_ball {d : ℕ} (k a : Frequency d)
    (hk : k ∈ torusCube d) (hout : k ∉ radiusBall d (3 / 10))
    (β : ℝ) (hβ : β ≤ 1 / 50) (hclose : ∀ j, 99 / 100 ≤ a j)
    (hδ : |amplitudeExcess a| ≤ 1 / 2500) :
    1 / 100 ≤ perturbedDispersion a 0 k + 2 * (d : ℝ) - β := by
  have hcoord : ∀ j, |k j| ≤ Real.pi := by
    intro j
    have hj := hk j
    simp only [torusCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hj
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  have hbottom := bottomEnergy_free_lower k hcoord
  have hpiSq : Real.pi ^ 2 < 10 := by
    have hpi : Real.pi < (63 / 20 : ℝ) := by
      convert Real.pi_lt_d2 using 1 <;> norm_num
    have hsq := (sq_lt_sq₀ (le_of_lt Real.pi_pos) (by norm_num : 0 ≤ (63 / 20 : ℝ))).2 hpi
    nlinarith
  have hcoef : (2 / 5 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith
  have hout' : ¬ radius k ≤ 3 / 10 := by
    simpa [radiusBall] using hout
  have hr : 3 / 10 < radius k := lt_of_not_ge hout'
  have hr2 : (3 / 10 : ℝ) ^ 2 < radius k ^ 2 := by
    nlinarith [sq_nonneg (radius k - 3 / 10)]
  have hfree : (9 / 250 : ℝ) ≤ bottomEnergy (fun _ : Fin d => (1 : ℝ)) k := by
    calc
      9 / 250 = (2 / 5 : ℝ) * (3 / 10) ^ 2 := by norm_num
      _ ≤ (2 / 5 : ℝ) * radius k ^ 2 :=
        mul_le_mul_of_nonneg_left hr2.le (by norm_num)
      _ ≤ (4 / Real.pi ^ 2) * radius k ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ bottomEnergy (fun _ : Fin d => (1 : ℝ)) k := hbottom
  have hterms : ∀ j, (99 / 100 : ℝ) * (1 - Real.cos (k j)) ≤
      a j * (1 - Real.cos (k j)) := by
    intro j
    have hc : 0 ≤ 1 - Real.cos (k j) := by nlinarith [Real.cos_le_one (k j)]
    exact mul_le_mul_of_nonneg_right (hclose j) hc
  have hsum : ∑ j : Fin d, (99 / 100 : ℝ) * (1 - Real.cos (k j)) ≤
      ∑ j, a j * (1 - Real.cos (k j)) :=
    Finset.sum_le_sum (fun j _ => hterms j)
  have hbottomPert : (99 / 100 : ℝ) *
      bottomEnergy (fun _ : Fin d => (1 : ℝ)) k ≤ bottomEnergy a k := by
    unfold bottomEnergy
    calc
      (99 / 100 : ℝ) * (2 * ∑ j, 1 * (1 - Real.cos (k j))) =
          2 * ∑ j, (99 / 100 : ℝ) * (1 - Real.cos (k j)) := by
        calc
          (99 / 100 : ℝ) * (2 * ∑ j, 1 * (1 - Real.cos (k j))) =
              2 * ((99 / 100 : ℝ) * ∑ j, (1 - Real.cos (k j))) := by ring
          _ = 2 * ∑ j, (99 / 100 : ℝ) * (1 - Real.cos (k j)) := by
            rw [Finset.mul_sum]
      _ ≤ 2 * ∑ j, a j * (1 - Real.cos (k j)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hidentity := bottomEnergy_eq_perturbed a k
  have hshift := amplitudeShift_identity a
  have hpertEq : perturbedDispersion a 0 k + 2 * (d : ℝ) =
      bottomEnergy a k - amplitudeExcess a := by
    linarith
  have hfreePert : (99 / 100 : ℝ) * (9 / 250 : ℝ) ≤ bottomEnergy a k :=
    le_trans (mul_le_mul_of_nonneg_left hfree (by norm_num)) hbottomPert
  have hδhigh : amplitudeExcess a ≤ 1 / 2500 := (abs_le.mp hδ).2
  nlinarith

private theorem resolvent_norm_le_of_gap (x β v : ℝ) (hgap : 1 / 100 ≤ x - β) :
    ‖(((x - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖ ≤ 100 := by
  let z : ℂ := ((x - β : ℝ) : ℂ) - v * Complex.I
  have hre : z.re = x - β := by simp [z]
  have hnorm : 1 / 100 ≤ ‖z‖ := by
    calc
      1 / 100 ≤ x - β := hgap
      _ = |z.re| := by rw [hre, abs_of_nonneg (by linarith [hgap])]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  change ‖z⁻¹‖ ≤ 100
  rw [norm_inv]
  calc
    ‖z‖⁻¹ ≤ (1 / 100 : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 100) hnorm
    _ = 100 := by norm_num

private theorem resolvent_square_norm_le_of_gap (x β v : ℝ)
    (hgap : 1 / 100 ≤ x - β) :
    ‖((((x - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2‖ ≤ 10000 := by
  have h := resolvent_norm_le_of_gap x β v hgap
  calc
    ‖((((x - β : ℝ) : ℂ) - v * Complex.I)⁻¹) ^ 2‖ =
        ‖(((x - β : ℝ) : ℂ) - v * Complex.I)⁻¹‖ ^ 2 := norm_pow _ _
    _ ≤ 100 ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 h
    _ = 10000 := by norm_num

private theorem norm_integral_indicator_ofReal {d : ℕ} (s : Set (Frequency d))
    (hs : MeasurableSet s) (f : Frequency d → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ‖∫ k, ((Set.indicator s f k : ℝ) : ℂ)‖ = ∫ k in s, f k := by
  rw [norm_integral_complex_ofReal_of_nonneg volume (Set.indicator s f) (by
    intro k
    by_cases hk : k ∈ s
    · simp [Set.indicator_of_mem hk, hf k]
    · simp [Set.indicator_of_notMem hk])]
  rw [integral_indicator hs]

/-- Lemma 3.5 follows from the one-dimensional ray and polar statements. -/
theorem bottomResolvent_of_helpers (hRay : RayEstimatesStatement)
    (hPolar : PolarRayBoundStatement) : BottomResolventStatement := by
  intro d hd β₁ β₂ hβ₁ hβ₁₂ hβ₂
  have hd2 : 2 ≤ d := by omega
  obtain ⟨σ, hσ, hpolarUpper, hpolarLower⟩ := hPolar d hd2
  let βlo : ℝ := β₁ / 2
  let βhi : ℝ := β₂ + β₁ / 8
  let μ : ℝ := β₁ / 8
  have hβlo : 0 < βlo := by dsimp [βlo]; positivity
  have hβlohi : βlo ≤ βhi := by dsimp [βlo, βhi]; linarith
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hend : βhi + μ ≤ 1 / 40 := by
    dsimp [βhi, μ]
    nlinarith [hβ₁₂.trans hβ₂]
  obtain ⟨Cr, cr, hCr, hcr, hcore⟩ :=
    ray_core_estimates_of_helpers d hd βlo βhi μ hβlo hβlohi hμ hend hRay
  let ε : ℝ := β₁ / (100 * (d : ℝ))
  have hε : 0 < ε := by
    dsimp [ε]
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hεsmall : ε ≤ 1 / 100 := by
    dsimp [ε]
    have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (d : ℝ))]
    nlinarith [hβ₁₂.trans hβ₂]
  have hdne : (d : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (show 0 < d by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let V : ℝ := volume.real (torusCube d)
  have hV : 0 ≤ V := by dsimp [V]; exact ENNReal.toReal_nonneg
  have hvol : volume (torusCube d) ≠ ∞ := torusCube_volume_ne_top d
  let C : ℝ := 1 + σ * Cr + 100 * V + 10000 * V * (Real.log 2)⁻¹
  let c : ℝ := σ * cr
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨ε, C, c, hε, hC, hc, ?_⟩
  intro β hβ v hv hv1
  have hβcore : β ∈ Set.Icc βlo βhi := by
    constructor
    · dsimp [βlo]
      linarith [hβ.1]
    · dsimp [βhi]
      linarith [hβ.2]
  have hratio : 1 < 2 / v := by
    rw [lt_div_iff₀ hv]
    nlinarith [hv1]
  have hlog : 0 < Real.log (2 / v) := Real.log_pos hratio
  have htwo_le_ratio : 2 ≤ 2 / v := by
    rw [le_div_iff₀ hv]
    nlinarith [hv1]
  have hlogmono : Real.log 2 ≤ Real.log (2 / v) :=
    Real.log_le_log (by norm_num) htwo_le_ratio
  have hlogscale : 1 ≤ (Real.log 2)⁻¹ * Real.log (2 / v) := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := (inv_mul_cancel₀ (ne_of_gt hlog2)).symm
      _ ≤ (Real.log 2)⁻¹ * Real.log (2 / v) :=
        mul_le_mul_of_nonneg_left hlogmono (inv_nonneg.mpr hlog2.le)
  have htail : 10000 * V ≤
      (10000 * V * (Real.log 2)⁻¹) * Real.log (2 / v) := by
    have h := mul_le_mul_of_nonneg_left hlogscale (by positivity : 0 ≤ 10000 * V)
    nlinarith [h]
  let fAbs : Frequency d → ℝ := freeResolventAbs β v
  let fFirst : Frequency d → ℂ := freeResolvent β v
  let fImag : Frequency d → ℝ := freeImaginaryDensity β v
  have hfAbsNonneg (k : Frequency d) : 0 ≤ fAbs k := by
    dsimp [fAbs, freeResolventAbs]
    exact norm_nonneg _
  have hfAbsBound (k : Frequency d) : ‖fAbs k‖ ≤ v⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfAbsNonneg k)]
    exact freeResolvent_norm_bound β v hv k
  have hfFirstBound (k : Frequency d) : ‖fFirst k‖ ≤ v⁻¹ :=
    freeResolvent_norm_bound β v hv k
  have hfImagNonneg (k : Frequency d) : 0 ≤ fImag k :=
    freeImaginaryDensity_nonneg β v hv k
  have hfImagBound (k : Frequency d) : ‖fImag k‖ ≤ v⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfImagNonneg k)]
    exact freeImaginaryDensity_bound β v hv k
  have hfAbsMeas : AEStronglyMeasurable fAbs volume :=
    (freeResolventAbs_continuous β v hv).aestronglyMeasurable
  have hfFirstMeas : AEStronglyMeasurable fFirst volume :=
    (freeResolvent_continuous β v hv).aestronglyMeasurable
  have hfImagMeas : AEStronglyMeasurable fImag volume :=
    (freeImaginaryDensity_continuous β v hv).aestronglyMeasurable
  have hfAbsCube : IntegrableOn fAbs (torusCube d) volume :=
    integrableOn_of_bounded_on_torusCube fAbs hfAbsMeas (v⁻¹) hfAbsBound
  have hfFirstCube : IntegrableOn fFirst (torusCube d) volume :=
    integrableOn_of_bounded_on_torusCube fFirst hfFirstMeas (v⁻¹) hfFirstBound
  have hfImagCube : IntegrableOn fImag (torusCube d) volume :=
    integrableOn_of_bounded_on_torusCube fImag hfImagMeas (v⁻¹) hfImagBound
  have hfAbsBall : IntegrableOn fAbs (radiusBall d (3 / 10)) volume :=
    integrableOn_of_bounded_on_radiusBall (3 / 10) fAbs hfAbsMeas (v⁻¹) hfAbsBound
  have hfFirstBall : IntegrableOn fFirst (radiusBall d (3 / 10)) volume :=
    integrableOn_of_bounded_on_radiusBall (3 / 10) fFirst hfFirstMeas (v⁻¹) hfFirstBound
  have hfImagBall : IntegrableOn fImag (radiusBall d (3 / 10)) volume :=
    integrableOn_of_bounded_on_radiusBall (3 / 10) fImag hfImagMeas (v⁻¹) hfImagBound
  have hunitAmplitude : ∀ j : Fin d, 3 / 4 ≤ (fun _ : Fin d => (1 : ℝ)) j ∧
      (fun _ : Fin d => (1 : ℝ)) j ≤ 5 / 4 := by
    intro j
    constructor <;> norm_num
  have hcoreFree (ω : Frequency d) (hω : ∑ j, ω j ^ 2 = 1) :=
    hcore (fun _ : Fin d => (1 : ℝ)) ω hunitAmplitude hω β hβcore v hv hv1
  have hradAbs (ω : Frequency d) (hω : ∑ j, ω j ^ 2 = 1) :
      ‖∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
        (fAbs (r • ω) : ℂ)‖ ≤ Cr * Real.log (2 / v) := by
    let g : ℝ → ℝ := fun r => r ^ (d - 1) * fAbs (r • ω)
    have hnonneg : ∀ r ∈ Set.Icc (0 : ℝ) (3 / 10), 0 ≤ g r := by
      intro r hr
      exact mul_nonneg (pow_nonneg hr.1 _) (hfAbsNonneg (r • ω))
    have hfun : ∀ r,
        ((r ^ (d - 1) : ℝ) : ℂ) * (fAbs (r • ω) : ℂ) = (g r : ℂ) := by
      intro r
      simp [g, Complex.ofReal_mul]
    have hcast :
        (∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
          (fAbs (r • ω) : ℂ)) = ∫ r in (0 : ℝ)..(3 / 10), (g r : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall (fun r _ => hfun r)
    calc
      _ = ‖∫ r in (0 : ℝ)..(3 / 10), (g r : ℂ)‖ := by rw [hcast]
      _ = ∫ r in (0 : ℝ)..(3 / 10), g r :=
        norm_interval_integral_complex_ofReal_of_nonneg (by norm_num) hnonneg
      _ ≤ Cr * Real.log (2 / v) := by
        simpa [g, fAbs, freeResolventAbs, freeResolvent_eq_ray] using
          (hcoreFree ω hω).2.1
  have hradFirst (ω : Frequency d) (hω : ∑ j, ω j ^ 2 = 1) :
      ‖∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
        fFirst (r • ω)‖ ≤ Cr := by
    simpa [fFirst, freeResolvent_eq_ray] using (hcoreFree ω hω).2.2.1
  have hradImag (ω : Frequency d) (hω : ∑ j, ω j ^ 2 = 1) :
      cr ≤ ∫ r in (0 : ℝ)..(3 / 10), r ^ (d - 1) * fImag (r • ω) := by
    simpa [fImag, freeImaginaryDensity_eq_ray] using (hcoreFree ω hω).2.2.2
  let fAbsC : Frequency d → ℂ := fun k => (fAbs k : ℂ)
  have hfAbsCMeas : AEStronglyMeasurable fAbsC volume := by
    exact (Complex.continuous_ofReal.comp (freeResolventAbs_continuous β v hv)).aestronglyMeasurable
  have hfAbsCbound (k : Frequency d) : ‖fAbsC k‖ ≤ v⁻¹ := by
    simpa [fAbsC, fAbs, freeResolventAbs] using freeResolvent_norm_bound β v hv k
  have hfAbsIndicator : Integrable (Set.indicator (radiusBall d (3 / 10)) fAbsC) volume :=
    integrable_indicator_radiusBall fAbsC hfAbsCMeas hfAbsCbound
  have hAbsIndicatorEq :
      ‖∫ k, Set.indicator (radiusBall d (3 / 10)) fAbsC k‖ =
        ∫ k in radiusBall d (3 / 10), fAbs k := by
    have hfun : Set.indicator (radiusBall d (3 / 10)) fAbsC =
        fun k => ((Set.indicator (radiusBall d (3 / 10)) fAbs k : ℝ) : ℂ) := by
      funext k
      by_cases hk : k ∈ radiusBall d (3 / 10)
      · simp [fAbsC, Set.indicator_of_mem hk]
      · simp [fAbsC, Set.indicator_of_notMem hk]
    rw [hfun]
    exact norm_integral_indicator_ofReal _ (measurableSet_radiusBall d (3 / 10))
      fAbs hfAbsNonneg
  have hAbsPolar := polar_upper_radiusBall σ (Cr * Real.log (2 / v)) (3 / 10)
    hpolarUpper (by norm_num) fAbsC hfAbsIndicator hradAbs
  have hAbsCentral : ∫ k in radiusBall d (3 / 10), fAbs k ≤
      σ * (Cr * Real.log (2 / v)) := by
    rw [← hAbsIndicatorEq]
    exact hAbsPolar
  have hfFirstIndicator : Integrable (Set.indicator (radiusBall d (3 / 10)) fFirst) volume :=
    integrable_indicator_radiusBall fFirst hfFirstMeas hfFirstBound
  have hFirstPolar := polar_upper_radiusBall σ Cr (3 / 10) hpolarUpper
    (by norm_num) fFirst hfFirstIndicator hradFirst
  have hFirstCentral : ‖∫ k in radiusBall d (3 / 10), fFirst k‖ ≤ σ * Cr := by
    rw [← integral_indicator (measurableSet_radiusBall d (3 / 10))]
    exact hFirstPolar
  have hfImagIndicator : Integrable (Set.indicator (radiusBall d (3 / 10)) fImag) volume :=
    integrable_indicator_radiusBall fImag hfImagMeas hfImagBound
  have hImagPolar := polar_lower_radiusBall σ cr (3 / 10) hpolarLower
    (by norm_num) fImag hfImagIndicator hfImagNonneg hradImag
  have hImagCentral : σ * cr ≤ ∫ k in radiusBall d (3 / 10), fImag k := by
    rw [← integral_indicator (measurableSet_radiusBall d (3 / 10))]
    exact hImagPolar
  have hAbsSplit := integral_torusCube_split fAbs hfAbsCube hfAbsBall
  have hFirstSplit := integral_torusCube_split fFirst hfFirstCube hfFirstBall
  have hImagSplit := integral_torusCube_split fImag hfImagCube hfImagBall
  have hAbsOuter : ∫ k in torusCube d \ radiusBall d (3 / 10), fAbs k ≤ 100 * V := by
    apply integral_nonneg_torusCube_remainder_le fAbs 100 hvol (by norm_num)
    · intro k hk
      exact hfAbsNonneg k
    · intro k hk
      change fAbs k ≤ 100
      exact resolvent_norm_le_of_gap (freeEnergy k) β v
        (free_energy_gap_outside_ball k hk.1 hk.2 β (by linarith [hβ.2, hβ₂]))
  have hFirstOuter : ‖∫ k in torusCube d \ radiusBall d (3 / 10), fFirst k‖ ≤ 100 * V := by
    apply norm_integral_torusCube_remainder_le fFirst 100 hvol (by norm_num)
    intro k hk
    exact resolvent_norm_le_of_gap (freeEnergy k) β v
      (free_energy_gap_outside_ball k hk.1 hk.2 β (by linarith [hβ.2, hβ₂]))
  have hImagOuterNonneg : 0 ≤ ∫ k in torusCube d \ radiusBall d (3 / 10), fImag k := by
    apply setIntegral_nonneg_of_ae_restrict
    apply (ae_restrict_iff' ((torusCube_measurableSet d).diff
      (measurableSet_radiusBall d (3 / 10)))).2
    exact Filter.Eventually.of_forall (fun k hk => hfImagNonneg k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (∫ k in torusCube d, fAbs k) ≤ C * Real.log (2 / v)
    rw [hAbsSplit]
    calc
      (∫ k in radiusBall d (3 / 10), fAbs k) +
          ∫ k in torusCube d \ radiusBall d (3 / 10), fAbs k ≤
        σ * (Cr * Real.log (2 / v)) + 100 * V := add_le_add hAbsCentral hAbsOuter
      _ ≤ C * Real.log (2 / v) := by
        dsimp [C]
        nlinarith [htail, hlog]
  · change ‖∫ k in torusCube d, fFirst k‖ ≤ C
    rw [hFirstSplit]
    calc
      ‖(∫ k in radiusBall d (3 / 10), fFirst k) +
          ∫ k in torusCube d \ radiusBall d (3 / 10), fFirst k‖ ≤
        ‖∫ k in radiusBall d (3 / 10), fFirst k‖ +
          ‖∫ k in torusCube d \ radiusBall d (3 / 10), fFirst k‖ := norm_add_le _ _
      _ ≤ σ * Cr + 100 * V := add_le_add hFirstCentral hFirstOuter
      _ ≤ C := by
        dsimp [C]
        nlinarith [hV]
  · change c ≤ ∫ k in torusCube d, fImag k
    rw [hImagSplit]
    dsimp [c]
    linarith
  · intro a φ ha
    have ha34 : ∀ j, 3 / 4 ≤ a j ∧ a j ≤ 5 / 4 :=
      amplitude_close_bounds a ε (by nlinarith [hεsmall]) ha
    have hclose : ∀ j, 99 / 100 ≤ a j ∧ a j ≤ 101 / 100 := by
      intro j
      have hj := abs_le.mp (ha j)
      constructor
      · linarith [hj.1, hεsmall]
      · linarith [hj.2, hεsmall]
    have hδ : |amplitudeExcess a| ≤ β₁ / 50 := by
      calc
        |amplitudeExcess a| ≤ 2 * (d : ℝ) * ε :=
          amplitudeExcess_abs_le a ε ha (le_of_lt hε)
        _ = β₁ / 50 := by
          dsimp [ε]
          field_simp [hdne]
          ring
    have hδtiny : |amplitudeExcess a| ≤ 1 / 2500 := by
      linarith [hδ, hβ₁₂.trans hβ₂]
    let βeff : ℝ := β + amplitudeExcess a
    have hβeff : βeff ∈ Set.Icc βlo βhi := by
      have hδparts := abs_le.mp hδ
      constructor
      · dsimp [βeff, βlo]
        linarith [hβ.1, hδparts.1]
      · dsimp [βeff, βhi]
        linarith [hβ.2, hδparts.2]
    let fPert : Frequency d → ℂ := perturbedSquareKernel a β v
    have hEnergyCont : Continuous (fun k : Frequency d =>
        perturbedDispersion a 0 k + 2 * (d : ℝ)) := by
      unfold perturbedDispersion
      fun_prop
    have hfPertCont : Continuous fPert := by
      exact continuous_resolvent_square_of_continuous_energy
        (fun k => perturbedDispersion a 0 k + 2 * (d : ℝ)) hEnergyCont β v hv
    have hfPertBound (k : Frequency d) : ‖fPert k‖ ≤ (v⁻¹) ^ 2 := by
      have hres : ‖(((perturbedDispersion a 0 k + 2 * (d : ℝ) - β : ℝ) : ℂ) -
          v * Complex.I)⁻¹‖ ≤ v⁻¹ := by
        simpa only [Complex.ofReal_sub] using
          norm_resolvent_le (perturbedDispersion a 0 k + 2 * (d : ℝ)) β v hv
      change ‖(((perturbedDispersion a 0 k + 2 * (d : ℝ) - β : ℝ) : ℂ) -
        v * Complex.I)⁻¹ ^ 2‖ ≤ (v⁻¹) ^ 2
      rw [norm_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr hv.le)).2 hres
    have hfPertMeas : AEStronglyMeasurable fPert volume := hfPertCont.aestronglyMeasurable
    have hfPertCube : IntegrableOn fPert (torusCube d) volume :=
      integrableOn_of_bounded_on_torusCube fPert hfPertMeas ((v⁻¹) ^ 2) hfPertBound
    have hfPertBall : IntegrableOn fPert (radiusBall d (3 / 10)) volume :=
      integrableOn_of_bounded_on_radiusBall (3 / 10) fPert hfPertMeas ((v⁻¹) ^ 2) hfPertBound
    have hradPert (ω : Frequency d) (hω : ∑ j, ω j ^ 2 = 1) :
        ‖∫ r in (0 : ℝ)..(3 / 10), ((r ^ (d - 1) : ℝ) : ℂ) *
          fPert (r • ω)‖ ≤ Cr * Real.log (2 / v) := by
      have h := hcore a ω ha34 hω βeff hβeff v hv hv1
      simpa [fPert, perturbedSquareKernel, βeff, rayEnergy_perturbed_denominator] using h.1
    have hfPertIndicator : Integrable (Set.indicator (radiusBall d (3 / 10)) fPert) volume :=
      integrable_indicator_radiusBall fPert hfPertMeas hfPertBound
    have hPertPolar := polar_upper_radiusBall σ (Cr * Real.log (2 / v)) (3 / 10)
      hpolarUpper (by norm_num) fPert hfPertIndicator hradPert
    have hPertCentral : ‖∫ k in radiusBall d (3 / 10), fPert k‖ ≤
        σ * (Cr * Real.log (2 / v)) := by
      rw [← integral_indicator (measurableSet_radiusBall d (3 / 10))]
      exact hPertPolar
    have hPertSplit := integral_torusCube_split fPert hfPertCube hfPertBall
    have hPertOuter : ‖∫ k in torusCube d \ radiusBall d (3 / 10), fPert k‖ ≤
        10000 * V := by
      apply norm_integral_torusCube_remainder_le fPert 10000 hvol (by norm_num)
      intro k hk
      exact resolvent_square_norm_le_of_gap
        (perturbedDispersion a 0 k + 2 * (d : ℝ)) β v
        (perturbed_energy_gap_outside_ball k a hk.1 hk.2 β
          (by linarith [hβ.2, hβ₂]) (fun j => (hclose j).1) hδtiny)
    have hperiod : ∀ g ∈ periodLattice d, ∀ k, fPert (g + k) = fPert k := by
      intro g hg k
      exact perturbedSquareKernel_periodic_lattice a β v g hg k
    have hphase := integral_periodic_phase_shift d fPert φ hperiod
    have htranslated :
        (∫ k in torusCube d,
          ((((perturbedDispersion a φ k + 2 * (d : ℝ) - β : ℝ) : ℂ) -
            v * Complex.I)⁻¹) ^ 2) = ∫ k in torusCube d, fPert k := by
      calc
        _ = ∫ k in torusCube d, fPert (k + φ) := by
          apply setIntegral_congr_fun (torusCube_measurableSet d)
          intro k hk
          simp [fPert, perturbedSquareKernel, perturbedDispersion, Pi.add_apply]
        _ = ∫ k in torusCube d, fPert k := hphase
    calc
      ‖∫ k in torusCube d,
          ((((perturbedDispersion a φ k + 2 * (d : ℝ) - β : ℝ) : ℂ) -
            v * Complex.I)⁻¹) ^ 2‖ = ‖∫ k in torusCube d, fPert k‖ :=
          congrArg norm htranslated
      _ ≤ σ * (Cr * Real.log (2 / v)) + 10000 * V := by
        rw [hPertSplit]
        calc
          ‖(∫ k in radiusBall d (3 / 10), fPert k) +
              ∫ k in torusCube d \ radiusBall d (3 / 10), fPert k‖ ≤
            ‖∫ k in radiusBall d (3 / 10), fPert k‖ +
              ‖∫ k in torusCube d \ radiusBall d (3 / 10), fPert k‖ := norm_add_le _ _
          _ ≤ σ * (Cr * Real.log (2 / v)) + 10000 * V :=
            add_le_add hPertCentral hPertOuter
      _ ≤ C * Real.log (2 / v) := by
        dsimp [C]
        nlinarith [htail, hlog]


end AndersonAC.S3
