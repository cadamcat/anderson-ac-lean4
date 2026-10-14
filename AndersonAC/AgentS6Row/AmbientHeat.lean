import AndersonAC.AgentS6Row.Ambient

noncomputable section
open Matrix Finset ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The heat vector, zero on inactive coordinates. -/
def ambientV {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (x : ι) (hx : x ∈ s.active) : ι → ℂ :=
  fun i => if hi : i ∈ s.active then
    scaledInverse t (trialInverse t r s) ⟨i, hi⟩ ⟨x, hx⟩ *
      (Real.sqrt ((r i).im / (r x).im) : ℂ) else 0

lemma ambientV_active {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (x : ι) (hx : x ∈ s.active) (i : s.active) :
    ambientV t r s x hx i = heatVec s.M t (fun j : s.active => r j) ⟨x, hx⟩ i := by
  simp only [ambientV, dif_pos i.2, heatVec, scaledInverse, Matrix.smul_apply, smul_eq_mul]
  rfl

lemma ambientV_inactive {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (x : ι) (hx : x ∈ s.active) (i : ι) (hi : i ∉ s.active) :
    ambientV t r s x hx i = 0 := by simp [ambientV, hi]

lemma ambientV_scattering {core : Finset ι} {t : ℝ} (ht : 0 < t) (r : ι → ℂ)
    (hr : ∀ i, 0 < (r i).im) (s : TrialState core) (x : ι) (hx : x ∈ s.active)
    (i : ι) (hix : i ≠ x) :
    ambientV t r s x hx i =
      (1 / (2 * Complex.I * (Real.sqrt t : ℂ) * ((r x).im : ℂ))) *
        ambientScattering t r s i x := by
  by_cases hi : i ∈ s.active
  · rw [show ambientScattering t r s i x =
        scat t (pim (fun j : s.active => r j))
          (damped s.M t (fun j : s.active => r j))⁻¹ ⟨i, hi⟩ ⟨x, hx⟩ by
          simp [ambientScattering, extendBlock, hi, hx]; rfl]
    rw [ambientV_active t r s x hx ⟨i, hi⟩]
    exact heatVec_eq (M := s.M) (r := fun j : s.active => r j) ht
      (fun j : s.active => hr j) (⟨x, hx⟩ : s.active)
      (fun h => hix (congrArg Subtype.val h))
  · simp [ambientV, ambientScattering, extendBlock, hi, hix]

lemma ambientV_sq_le {core : Finset ι} {t C c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (r : ι → ℂ) (hr : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C)
    (s : TrialState core) (x : ι) (hx : x ∈ s.active)
    (hpre : HeatPrestate t C (fun i : s.active => r i) (trialInverse t r s)) (i : ι) :
    ‖ambientV t r s x hx i‖ ^ 2 ≤ C / c * Real.sqrt (fourthCap t) := by
  have hC : 0 ≤ C := hc.le.trans (hr x).1 |>.trans (hr x).2
  by_cases hi : i ∈ s.active
  · rw [ambientV_active t r s x hx ⟨i, hi⟩]
    exact (norm_sq_heatVec_le (M := s.M) (r := fun j : s.active => r j)
      (x := ⟨x, hx⟩) ht (fun j : s.active => hr j) hc s.symmetric ⟨i, hi⟩).trans
      (mul_le_mul_of_nonneg_left (norm_sq_h_le_sqrt ht (hpre.2.2 ⟨x, hx⟩) ⟨i, hi⟩)
        (div_nonneg hC hc.le))
  · rw [ambientV_inactive t r s x hx i hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity

lemma ambientV_sum_sq {core : Finset ι} {t : ℝ} (ht : 0 < t) (r : ι → ℂ)
    (hr : ∀ i, 0 < (r i).im) (s : TrialState core) (x : ι) (hx : x ∈ s.active) :
    ∑ i, ‖ambientV t r s x hx i‖ ^ 2 = (trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩).im / (r x).im := by
  calc
    _ = ∑ i ∈ s.active, ‖ambientV t r s x hx i‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [ambientV, hi]
    _ = ∑ i : s.active, ‖heatVec s.M t (fun j : s.active => r j) ⟨x, hx⟩ i‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      exact Finset.sum_congr rfl fun i _ => by rw [ambientV_active]
    _ = _ := sum_norm_sq_heatVec s.symmetric ht (fun i => hr i)

lemma ambientHeat_vn_bound {core : Finset ι} {t C c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (r : ι → ℂ) (hr : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C)
    (s : TrialState core) (x : ι) (hx : x ∈ s.active) (hxc : x ∉ core)
    (L : Matrix core core ℂ)
    (hpre : HeatPrestate t C (fun i : s.active => r i) (trialInverse t r s)) :
    |(nheat (ambientScattering t r s) L x (ambientV t r s x hx)).vn - 1| ≤
      C * t ^ betaW / c + (core.card + 1) * (C / c * Real.sqrt (fourthCap t)) := by
  set W : ι → ℝ := fun i => ‖ambientV t r s x hx i‖ ^ 2
  have hW0 : ∀ i, 0 ≤ W i := fun _ => sq_nonneg _
  have hWle : ∀ i, W i ≤ C / c * Real.sqrt (fourthCap t) :=
    ambientV_sq_le ht hc r hr s x hx hpre
  have e1 : ∑ i, W i = (trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩).im / (r x).im :=
    ambientV_sum_sq ht r (fun i => hc.trans_le (hr i).1) s x hx
  have e2 : ∑ i, W i = ∑ i ∈ core, W i + (∑ i ∈ coreᶜ.erase x, W i + W x) := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_compl.mpr hxc), Finset.sum_add_sum_compl]
  have e3 : ∑ i ∈ core, W i + W x ≤ (core.card + 1) * (C / c * Real.sqrt (fourthCap t)) := by
    have hh := Finset.sum_le_card_nsmul core W _ (fun i _ => hWle i)
    rw [nsmul_eq_mul] at hh
    have := hWle x
    linarith
  have hpx : 0 < (r x).im := hc.trans_le (hr x).1
  have e4 : |(trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩).im / (r x).im - 1| ≤
      C * t ^ betaW / c := by
    rw [div_sub_one hpx.ne', abs_div, abs_of_pos hpx]
    calc
      _ ≤ ‖trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩ - r x‖ / (r x).im := by
        gcongr
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      _ ≤ ‖trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩ - r x‖ / c :=
        div_le_div_of_nonneg_left (norm_nonneg _) hc (hr x).1
      _ ≤ _ := div_le_div_of_nonneg_right (hpre.2.1 ⟨x, hx⟩) hc.le
  change |(∑ i ∈ coreᶜ.erase x, W i) - 1| ≤ _
  have he : (∑ i ∈ coreᶜ.erase x, W i) - 1 =
      ((trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩).im / (r x).im - 1) - (∑ i ∈ core, W i + W x) := by
    rw [← e1, e2]
    ring
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (add_nonneg (Finset.sum_nonneg (fun i _ => hW0 i)) (hW0 x))]
  exact add_le_add e4 e3

lemma ambientHeat_b_bound {core : Finset ι} {t c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (r : ι → ℂ) (hr : ∀ i, c ≤ (r i).im)
    (s : TrialState core) (x : ι) (hx : x ∈ s.active) (hxc : x ∉ core)
    (τ : ℝ) (hτ : 0 < τ) (L : Matrix core core ℂ)
    (hL : L * Lᴴ = (AndersonAC.L64.gram (ambientScattering t r s) core coreᶜ + (τ : ℂ) • 1)⁻¹) :
    nsq (nheat (ambientScattering t r s) L x (ambientV t r s x hx)).b ≤
      (nheat (ambientScattering t r s) L x (ambientV t r s x hx)).m / (t * c ^ 2) := by
  have hp : ∀ i, 0 < (r i).im := fun i => hc.trans_le (hr i)
  set κ : ℂ := 1 / (2 * Complex.I * (Real.sqrt t : ℂ) * ((r x).im : ℂ))
  have hv : ∀ i ∈ coreᶜ.erase x, ambientV t r s x hx i = κ * ambientScattering t r s i x :=
    fun i hi => ambientV_scattering ht r hp s x hx i (Finset.ne_of_mem_erase hi)
  have hh := nsq_b_le hτ hL (ambientScattering_unitary ht r hp s) (ambientScattering_symm t r s)
    hxc (ambientV t r s x hx) κ hv
  have hκ : ‖κ‖ ^ 2 = 1 / (4 * (t * (r x).im ^ 2)) := by
    simp only [κ, norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_I,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (hp x).le, RCLike.norm_ofNat]
    rw [div_pow, one_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht.le]
    ring
  rw [hκ] at hh
  have hm := nsq_nonneg (nheat (ambientScattering t r s) L x (ambientV t r s x hx)).ux
  calc
    _ ≤ _ := hh
    _ = (nheat (ambientScattering t r s) L x (ambientV t r s x hx)).m / (t * (r x).im ^ 2) := by
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left hm (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le (hr x) 2) ht.le

end AndersonAC.AgentS6Row
