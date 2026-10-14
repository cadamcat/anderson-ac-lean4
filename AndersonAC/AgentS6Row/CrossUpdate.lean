import AndersonAC.AgentS6Row.AmbientHeat

noncomputable section
open Matrix Finset ComplexConjugate

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trialCross_heat_update {core : Finset ι} {t : ℝ} (ht : 0 < t)
    (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) {s s' : TrialState core} {x : ι}
    {ξ : ℝ} (h : HeatTransition t r s s' x ξ) (hx : x ∈ s.active)
    (i : ι) (hic : i ∉ core) (hix : i ≠ x) :
    trialCross t r s' i = trialCross t r s i +
      (heatCoefficient t (r x) (trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩) ξ *
        ambientV t r s x hx i) • trialCross t r s x := by
  obtain ⟨hx', hq, hinv⟩ := AndersonAC.AgentS6.trial_heat_step ht r hr h
  obtain ⟨_, hxc, hact, _, _, _⟩ := h
  funext b
  by_cases hi : i ∈ s.active
  · have hi' : i ∈ s'.active := by rw [hact]; exact Finset.mem_erase.mpr ⟨hix, hi⟩
    have hb := s.core_active b.2
    have hb' := s'.core_active b.2
    have hib : (⟨i, hi⟩ : s.active) ≠ ⟨b, hb⟩ := by
      intro e
      apply hic
      have he : i = (b : ι) := congrArg Subtype.val e
      rw [he]
      exact b.2
    have hib' : (⟨i, hi'⟩ : s'.active) ≠ ⟨b, hb'⟩ := by
      intro e
      apply hic
      have he : i = (b : ι) := congrArg Subtype.val e
      rw [he]
      exact b.2
    have hxb : (⟨x, hx⟩ : s.active) ≠ ⟨b, hb⟩ := by
      intro e
      apply hxc
      have he : x = (b : ι) := congrArg Subtype.val e
      rw [he]
      exact b.2
    simp only [trialCross, dif_pos hi, dif_pos hi', dif_pos hx, if_neg hic, if_neg hxc,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show scattering t (fun j : s'.active => r j) (trialInverse t r s') =
        scat t (pim (fun j : s'.active => r j)) (trialInverse t r s') from rfl,
      show scattering t (fun j : s.active => r j) (trialInverse t r s) =
        scat t (pim (fun j : s.active => r j)) (trialInverse t r s) from rfl]
    rw [scat_apply_ne _ _ _ hib', scat_apply_ne _ _ _ hib, scat_apply_ne _ _ _ hxb,
      hinv ⟨i, hi'⟩ ⟨b, hb'⟩ hi hb]
    simp only [ambientV, dif_pos hi, scaledInverse, Matrix.smul_apply, smul_eq_mul, heatCoefficient, pim]
    have hpx := hr x
    have hsx : (Real.sqrt (r x).im : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpx).ne'
    have hst : (Real.sqrt t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
    rw [Real.sqrt_div' _ hpx.le]
    push_cast
    field_simp
    ring
  · have hi' : i ∉ s'.active := fun hh => hi (Finset.mem_of_mem_erase (hact ▸ hh))
    simp [trialCross, ambientV, hi, hi']

lemma ambientGram_post_eq {core : Finset ι} {t : ℝ} (r : ι → ℂ)
    {s s' : TrialState core} {x : ι} {ξ : ℝ} (h : HeatTransition t r s s' x ξ) :
    AndersonAC.L64.gram (ambientScattering t r s') core (coreᶜ.erase x) =
      AndersonAC.S6.gram (trialCross t r s') := by
  obtain ⟨hx, hxc, hact, _, _, _⟩ := h
  have hxn : x ∉ s'.active := by simp [hact]
  have hCzero : crossRow (ambientScattering t r s') core x = 0 := by
    rw [ambientCross_eq t r s' x hxc]
    funext b
    simp [trialCross, hxn]
  rw [← ambientGram_eq]
  unfold AndersonAC.L64.gram
  rw [← Finset.sum_erase_add _ _ (Finset.mem_compl.mpr hxc), hCzero]
  simp

lemma ambientLeverage_post_eq {core : Finset ι} {t : ℝ} (r : ι → ℂ)
    {s s' : TrialState core} {x : ι} {ξ : ℝ} (h : HeatTransition t r s s' x ξ)
    (τ : ℝ) (i : ι) (hic : i ∉ core) :
    ridgeLev (ambientScattering t r s') core (coreᶜ.erase x) τ i = trialWeights t r s' τ i := by
  unfold ridgeLev
  rw [ambientGram_post_eq r h]
  have hh := ambientLeverage_eq t r s' τ i hic
  unfold ridgeLev at hh
  rw [ambientGram_eq] at hh
  exact hh

lemma normalized_trial_row_update {core : Finset ι} {t : ℝ} (ht : 0 < t)
    (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) {s s' : TrialState core} {x : ι}
    {ξ : ℝ} (h : HeatTransition t r s s' x ξ) (hx : x ∈ s.active)
    (τ : ℝ) (hτ : 0 < τ) (L : Matrix core core ℂ)
    (hL : L * Lᴴ = (AndersonAC.L64.gram (ambientScattering t r s) core coreᶜ + (τ : ℂ) • 1)⁻¹)
    (i : ι) (hi : i ∈ coreᶜ.erase x) :
    let H := nheat (ambientScattering t r s) L x (ambientV t r s x hx)
    H.lev' (heatCoefficient t (r x) (trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩) ξ) i - H.lev i =
      trialWeights t r s' τ i - trialWeights t r s τ i := by
  dsimp only
  have hcopy := h
  obtain ⟨_, hxc, _, _, _, _⟩ := hcopy
  have hC : ∀ j ∈ coreᶜ.erase x,
      crossRow (ambientScattering t r s') core j = crossRow (ambientScattering t r s) core j +
        (heatCoefficient t (r x) (trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩) ξ *
          ambientV t r s x hx j) • crossRow (ambientScattering t r s) core x := by
    intro j hj
    have hjc := Finset.mem_compl.mp (Finset.mem_of_mem_erase hj)
    rw [ambientCross_eq t r s' j hjc, ambientCross_eq t r s j hjc,
      ambientCross_eq t r s x hxc]
    exact trialCross_heat_update ht r hr h hx j hjc (Finset.ne_of_mem_erase hj)
  rw [nheat_lev' _ hτ hL _ _ hC hxc hi, nheat_lev _ hτ hL,
    ambientLeverage_post_eq r h τ i (Finset.mem_compl.mp (Finset.mem_of_mem_erase hi)),
    ambientLeverage_eq t r s τ i (Finset.mem_compl.mp (Finset.mem_of_mem_erase hi))]

end AndersonAC.AgentS6Row
