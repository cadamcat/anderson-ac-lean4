import AndersonAC.S45.HelperStatements

open MeasureTheory
open scoped ENNReal

namespace AndersonAC.MuseS45ville

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} {b : ℝ}

/-- Hitting set up to time n: `∃ k ≤ n, b ≤ Z k`. -/
def hitSet (Z : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ k, k ≤ n ∧ b ≤ Z k ω}

theorem hitSet_eq_biUnion (Z : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) :
    hitSet Z b n = ⋃ k ∈ Finset.range (n + 1), {ω | b ≤ Z k ω} := by
  ext ω
  simp only [hitSet, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, hkn, hk⟩
    exact ⟨k, Nat.lt_succ_of_le hkn, hk⟩
  · rintro ⟨k, hkn, hk⟩
    exact ⟨k, Nat.le_of_lt_succ hkn, hk⟩

theorem hitSet_mono (Z : ℕ → Ω → ℝ) (b : ℝ) : Monotone (hitSet Z b) := by
  intro m n hmn ω hω
  obtain ⟨k, hkm, hk⟩ := hω
  exact ⟨k, le_trans hkm hmn, hk⟩

theorem hitSet_zero (Z : ℕ → Ω → ℝ) (b : ℝ) :
    hitSet Z b 0 = {ω | b ≤ Z 0 ω} := by
  ext ω
  simp only [hitSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hkn, hk⟩
    have : k = 0 := Nat.le_zero.mp hkn
    subst this
    exact hk
  · intro h
    exact ⟨0, le_refl 0, h⟩

theorem hitSet_iUnion (Z : ℕ → Ω → ℝ) (b : ℝ) :
    (⋃ n, hitSet Z b n) = {ω | ∃ n, b ≤ Z n ω} := by
  ext ω
  simp only [hitSet, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, k, _, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, k, le_refl k, hk⟩

theorem event_meas_filt (hadp : StronglyAdapted ℱ Z) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | b ≤ Z k ω} := by
  have hmeas : Measurable[ℱ k] (Z k) := hadp.adapted k
  have h : MeasurableSet[ℱ k] (Z k ⁻¹' Set.Ici b) := hmeas measurableSet_Ici
  exact h

theorem event_meas_le (hadp : StronglyAdapted ℱ Z) {k n : ℕ} (hkn : k ≤ n) :
    MeasurableSet[ℱ n] {ω | b ≤ Z k ω} :=
  (ℱ.mono hkn) _ (event_meas_filt hadp k)

theorem hitSet_meas_filt (hadp : StronglyAdapted ℱ Z) (n : ℕ) :
    MeasurableSet[ℱ n] (hitSet Z b n) := by
  rw [hitSet_eq_biUnion]
  apply Finset.measurableSet_biUnion
  intro k hk
  exact event_meas_le hadp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem hitSet_meas (hadp : StronglyAdapted ℱ Z) (n : ℕ) :
    MeasurableSet (hitSet Z b n) :=
  measurableSet_of_filtration (hitSet_meas_filt hadp n)

/-- The new mass `B \ A` sits inside the fresh exceedance event. -/
theorem diff_subset_event (Z : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) :
    hitSet Z b (n + 1) \ hitSet Z b n ⊆ {ω | b ≤ Z (n + 1) ω} := by
  intro ω hω
  obtain ⟨hB, hA⟩ := hω
  obtain ⟨k, hkn1, hk⟩ := hB
  by_cases hkn : k ≤ n
  · exact absurd (⟨k, hkn, hk⟩ : ω ∈ hitSet Z b n) hA
  · have : k = n + 1 := by omega
    subst this
    exact hk

/-- Key finite-horizon estimate by induction. -/
theorem hitSet_key (hmart : Supermartingale Z ℱ μ) (n : ℕ) :
    b * μ.real (hitSet Z b n)
      + ∫ ω in (hitSet Z b n)ᶜ, Z n ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
  have hadp : StronglyAdapted ℱ Z := hmart.stronglyAdapted
  induction n with
  | zero =>
    rw [hitSet_zero]
    have hF : MeasurableSet[ℱ 0] {ω | b ≤ Z 0 ω} := event_meas_filt hadp 0
    have hM : MeasurableSet {ω | b ≤ Z 0 ω} :=
      measurableSet_of_filtration hF
    have hint0 : Integrable (Z 0) μ := hmart.integrable 0
    have hconst : b * μ.real {ω | b ≤ Z 0 ω} ≤ ∫ ω in {ω | b ≤ Z 0 ω}, Z 0 ω ∂μ :=
      setIntegral_ge_of_const_le_real hM (measure_ne_top μ _)
        (fun x hx => hx) hint0.integrableOn
    have hadd : ∫ ω in {ω | b ≤ Z 0 ω}, Z 0 ω ∂μ
        + ∫ ω in {ω | b ≤ Z 0 ω}ᶜ, Z 0 ω ∂μ = ∫ ω, Z 0 ω ∂μ :=
      integral_add_compl hM hint0
    linarith
  | succ n ih =>
    set A : Set Ω := hitSet Z b n with hAdef
    set B : Set Ω := hitSet Z b (n + 1) with hBdef
    set Dset : Set Ω := B \ A with hDdef
    have hsub : A ⊆ B := hitSet_mono Z b (Nat.le_succ n)
    have hA_F : MeasurableSet[ℱ n] A := hitSet_meas_filt hadp n
    have hA_amb : MeasurableSet A := measurableSet_of_filtration hA_F
    have hB_F : MeasurableSet[ℱ (n + 1)] B := hitSet_meas_filt hadp (n + 1)
    have hB_amb : MeasurableSet B := measurableSet_of_filtration hB_F
    have hD_amb : MeasurableSet Dset := hB_amb.diff hA_amb
    have hAc_F : MeasurableSet[ℱ n] Aᶜ := hA_F.compl
    -- supermartingale step on the survival set
    have h_super : ∫ ω in Aᶜ, Z (n + 1) ω ∂μ ≤ ∫ ω in Aᶜ, Z n ω ∂μ :=
      hmart.setIntegral_le (Nat.le_succ n) hAc_F
    -- measure additivity: B = A ∪ Dset
    have hunion : A ∪ Dset = B := by
      ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro (h | ⟨h1, _⟩)
        · exact hsub h
        · exact h1
      · intro h
        by_cases ha : x ∈ A
        · exact Or.inl ha
        · exact Or.inr ⟨h, ha⟩
    have hdisjA : Disjoint A Dset := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1
    have hmu_add : μ (A ∪ Dset) = μ A + μ Dset := measure_union hdisjA hD_amb
    have hreal_add : μ.real B = μ.real A + μ.real Dset := by
      rw [← hunion, Measure.real_def, Measure.real_def, Measure.real_def, hmu_add]
      exact ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ Dset)
    -- integral splitting: Aᶜ = Bᶜ ∪ Dset
    have hcompl_union : Bᶜ ∪ Dset = Aᶜ := by
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_sdiff]
      constructor
      · rintro (h | ⟨h1, _⟩)
        · intro ha
          exact h (hsub ha)
        · intro ha
          exact ‹x ∉ A› ha
      · intro h
        by_cases hb : x ∈ B
        · exact Or.inr ⟨hb, h⟩
        · exact Or.inl hb
    have hdisjC : Disjoint Bᶜ Dset := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx1 hx2.1
    have hint1 : Integrable (Z (n + 1)) μ := hmart.integrable (n + 1)
    have hBc_amb : MeasurableSet Bᶜ := hB_amb.compl
    have hsplit : ∫ ω in Aᶜ, Z (n + 1) ω ∂μ
        = ∫ ω in Bᶜ, Z (n + 1) ω ∂μ + ∫ ω in Dset, Z (n + 1) ω ∂μ := by
      rw [← hcompl_union]
      exact setIntegral_union hdisjC hD_amb hint1.integrableOn hint1.integrableOn
    -- fresh mass bounded below by b
    have hdiff_mem : ∀ x ∈ Dset, b ≤ Z (n + 1) x := by
      intro x hx
      exact diff_subset_event Z b n hx
    have hdiff : b * μ.real Dset ≤ ∫ ω in Dset, Z (n + 1) ω ∂μ :=
      setIntegral_ge_of_const_le_real hD_amb (measure_ne_top μ Dset)
        hdiff_mem hint1.integrableOn
    -- combine
    have hB_eq : b * μ.real B = b * μ.real A + b * μ.real Dset := by
      rw [hreal_add]; ring
    linarith

end AndersonAC.MuseS45ville

namespace AndersonAC.OpusS45

theorem ville_proof : AndersonAC.SolS45.VilleStatement := by
  intro Ω mΩ μ hI ℱ Z D b hmart hnonneg hZ0 hD hb
  have hadp : StronglyAdapted ℱ Z := hmart.stronglyAdapted
  -- tail integrals are nonnegative
  have htail : ∀ n, 0 ≤ ∫ ω in (AndersonAC.MuseS45ville.hitSet Z b n)ᶜ, Z n ω ∂μ := by
    intro n
    apply setIntegral_nonneg_ae
      (measurableSet_of_filtration
        (AndersonAC.MuseS45ville.hitSet_meas_filt hadp n).compl)
    filter_upwards [hnonneg n] with ω hω _ using hω
  -- initial integral bounded by D
  have hint0 : Integrable (Z 0) μ := hmart.integrable 0
  have hZ0int : ∫ ω, Z 0 ω ∂μ ≤ D := by
    have hle : ∫ ω, Z 0 ω ∂μ ≤ ∫ _, D ∂μ :=
      integral_mono_ae hint0 (integrable_const D) hZ0
    have hconst : (∫ _, D ∂μ) = D := by simp [integral_const]
    linarith
  -- per-n real bound
  have hreal : ∀ n, b * (μ (AndersonAC.MuseS45ville.hitSet Z b n)).toReal ≤ D := by
    intro n
    have hkey := AndersonAC.MuseS45ville.hitSet_key (b := b) hmart n
    have ht := htail n
    rw [Measure.real_def] at hkey
    linarith
  -- per-n ENNReal bound
  have hbound : ∀ n, μ (AndersonAC.MuseS45ville.hitSet Z b n)
      ≤ ENNReal.ofReal (D / b) := by
    intro n
    have hfin : μ (AndersonAC.MuseS45ville.hitSet Z b n) ≠ ∞ :=
      measure_ne_top μ _
    have hle : (μ (AndersonAC.MuseS45ville.hitSet Z b n)).toReal ≤ D / b := by
      rw [le_div_iff₀ hb]
      have h := hreal n
      linarith [mul_comm b (μ (AndersonAC.MuseS45ville.hitSet Z b n)).toReal]
    calc μ (AndersonAC.MuseS45ville.hitSet Z b n)
          = ENNReal.ofReal (μ (AndersonAC.MuseS45ville.hitSet Z b n)).toReal :=
            (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (D / b) := ENNReal.ofReal_le_ofReal hle
  -- monotone union
  have hmono : Monotone (AndersonAC.MuseS45ville.hitSet Z b) :=
    AndersonAC.MuseS45ville.hitSet_mono Z b
  have hunion : (⋃ n, AndersonAC.MuseS45ville.hitSet Z b n)
      = {ω | ∃ n, b ≤ Z n ω} :=
    AndersonAC.MuseS45ville.hitSet_iUnion Z b
  calc μ {ω | ∃ n, b ≤ Z n ω}
        = μ (⋃ n, AndersonAC.MuseS45ville.hitSet Z b n) := by rw [hunion]
    _ = ⨆ n, μ (AndersonAC.MuseS45ville.hitSet Z b n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (D / b) := iSup_le hbound

end AndersonAC.OpusS45
