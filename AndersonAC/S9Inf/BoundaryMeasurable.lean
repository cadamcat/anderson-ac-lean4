import AndersonAC.S9Inf.HelperStatements
import Mathlib

/-! Measurability of finite vertical boundary events.

Route (lead sol-s9inf): restrict positive heights to dense rational heights;
continuity of each height section recovers the full vertical filter
(`𝓝[>] 0`); use `MeasureTheory.measurableSet_exists_tendsto` on the
countable comap filter and a measurable chosen limit (`limUnder`) to test
`Im > 0`, `Im = 0` and `limit ≠ 0`.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology

namespace AndersonAC.SolS9Inf

/-- Positive rational heights, viewed as reals. Countable dense subset of `Ioi 0`. -/
abbrev QPos : Type := { q : ℚ // 0 < (q : ℝ) }

instance : Countable QPos := Subtype.countable

/-- Inclusion of positive rational heights into `ℝ`. -/
abbrev qHeight : QPos → ℝ := fun q => (q.val : ℝ)

lemma qHeight_pos (q : QPos) : 0 < qHeight q := q.property

/-- The countable filter of rational heights tending to `0` from above. -/
abbrev ratFilter : Filter QPos := Filter.comap qHeight (nhdsWithin (0 : ℝ) (Set.Ioi 0))

instance ratFilter_countGen : ratFilter.IsCountablyGenerated := by
  unfold ratFilter
  infer_instance

instance ratFilter_neBot : NeBot ratFilter := by
  unfold ratFilter
  rw [Filter.comap_neBot_iff]
  intro t ht
  obtain ⟨ε, hεpos, hsub⟩ := Metric.mem_nhdsWithin_iff.mp ht
  obtain ⟨q, h0q, hqε⟩ := exists_rat_btwn (show (0 : ℝ) < ε from hεpos)
  refine ⟨⟨q, h0q⟩, ?_⟩
  apply hsub
  refine ⟨?_, h0q⟩
  simp only [qHeight, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos h0q]
  exact hqε

/-- Continuity on `Ioi 0` promotes convergence on dense rational heights to
convergence along the full vertical filter. Forward direction is composition
with `tendsto_comap`; reverse uses closed-ball approximation via continuity. -/
theorem tendsto_nhdsWithin_zero_iff_rat (g : ℝ → ℂ)
    (hg : ContinuousOn g (Set.Ioi (0 : ℝ))) (w : ℂ) :
    Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ↔
      Tendsto (fun q : QPos => g (qHeight q)) ratFilter (𝓝 w) := by
  constructor
  · intro h
    exact h.comp Filter.tendsto_comap
  · intro h
    rw [Metric.tendsto_nhds] at h ⊢
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hev : ∀ᶠ _x : QPos in ratFilter, dist (g (qHeight _x)) w < ε / 2 :=
      h (ε / 2) hε2
    have hev_mem : { q : QPos | dist (g (qHeight q)) w < ε / 2 } ∈ ratFilter := hev
    unfold ratFilter at hev_mem
    obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.mp hev_mem
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp ht
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Metric.ball (0 : ℝ) δ, Metric.ball_mem_nhds 0 hδpos, ?_⟩
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hx ⊢
    -- hx : x ∈ ball 0 δ ∩ Ioi 0; goal : dist (g x) w < ε
    obtain ⟨hxball, hxIoi⟩ := hx
    have hx0 : (0 : ℝ) < x := hxIoi
    have hxdist : dist x (0 : ℝ) < δ := Metric.mem_ball.mp hxball
    rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hxdist
    -- continuity at x
    have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx0
    have hIoi_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 x :=
      isOpen_Ioi.mem_nhds hxmem
    have hcat : ContinuousAt g x := hg.continuousAt hIoi_nhds
    have hev_cont : ∀ᶠ y in 𝓝 x, dist (g y) (g x) < ε / 2 :=
      Metric.tendsto_nhds.mp hcat (ε / 2) hε2
    obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hev_cont
    -- rational point in (max 0 (x - η/2)) .. (min δ (x + η/2))
    set a : ℝ := max 0 (x - η / 2) with ha
    set b : ℝ := min δ (x + η / 2) with hb
    have hη2 : (0 : ℝ) < η / 2 := half_pos hηpos
    have ha_lt_x : a < x := by
      rw [ha]
      apply max_lt hx0
      linarith
    have hx_lt_b : x < b := by
      rw [hb]
      apply lt_min hxdist
      linarith
    have hab : a < b := lt_trans ha_lt_x hx_lt_b
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (le_max_left 0 _) haq
    set qp : QPos := ⟨q, hq0⟩ with hqp
    have hq_eq : qHeight qp = (q : ℝ) := rfl
    have hq_mem_t : qHeight qp ∈ t := by
      apply hδsub
      rw [hq_eq]
      constructor
      · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq0]
        calc (q : ℝ) < b := hqb
          _ ≤ δ := min_le_left _ _
      · exact hq0
    have hdist_qw : dist (g (qHeight qp)) w < ε / 2 := hsub hq_mem_t
    have hdist_yx : dist (qHeight qp) x < η := by
      rw [hq_eq, Real.dist_eq]
      rw [abs_lt]
      constructor
      · -- -(η) < q - x; suffices -(η/2) < q - x
        have h1 : x - η / 2 ≤ a := le_max_right _ _
        have h2 : a < (q : ℝ) := haq
        linarith
      · have h1 : (q : ℝ) < b := hqb
        have h2 : b ≤ x + η / 2 := min_le_right _ _
        linarith
    have hdist_g : dist (g (qHeight qp)) (g x) < ε / 2 := hη hdist_yx
    calc dist (g x) w
        ≤ dist (g x) (g (qHeight qp)) + dist (g (qHeight qp)) w :=
          dist_triangle _ _ _
      _ = dist (g (qHeight qp)) (g x) + dist (g (qHeight qp)) w := by
          rw [dist_comm (g x) _]
      _ < ε / 2 + ε / 2 := add_lt_add hdist_g hdist_qw
      _ = ε := add_halves ε

theorem boundaryEventMeasurability_proof : BoundaryEventMeasurabilityStatement := by
  unfold BoundaryEventMeasurabilityStatement
  intro Ω _ f hmeas hcont
  -- rational sections
  set F : QPos → Ω → ℂ := fun q ω => f ω (qHeight q) with hF
  have hFmeas : ∀ q : QPos, Measurable (F q) := by
    intro q
    have hq : 0 < qHeight q := qHeight_pos q
    have h := hmeas (qHeight q) hq
    simpa [hF] using h
  -- countable convergence event
  have hEcnt : MeasurableSet { ω : Ω | ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) } :=
    MeasureTheory.measurableSet_exists_tendsto hFmeas
  -- per-point equivalence
  have hiff : ∀ ω : Ω, (∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w)) ↔
      (∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c)) := by
    intro ω
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, (tendsto_nhdsWithin_zero_iff_rat (f ω) (hcont ω) w).mp hw⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, (tendsto_nhdsWithin_zero_iff_rat (f ω) (hcont ω) c).mpr hc⟩
  have hEfull_eq : { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) } =
      { ω : Ω | ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) } := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact hiff ω
  have hEfull : MeasurableSet { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) } := by
    rw [hEfull_eq]
    exact hEcnt
  -- measurable chosen limit
  set G : Ω → ℂ := fun ω => Filter.limUnder ratFilter (fun q => F q ω) with hG
  have hGstrong : StronglyMeasurable G := by
    apply MeasureTheory.StronglyMeasurable.limUnder
    intro q
    exact (hFmeas q).stronglyMeasurable
  have hGmeas : Measurable G := hGstrong.measurable
  have hGspec : ∀ ω : Ω, (∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c)) →
      Tendsto (fun q => F q ω) ratFilter (𝓝 (G ω)) := by
    intro ω hex
    have h := tendsto_nhds_limUnder hex
    simpa [hG] using h
  have hGfull : ∀ ω : Ω, (∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c)) →
      Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (G ω)) := by
    intro ω hex
    exact (tendsto_nhdsWithin_zero_iff_rat (f ω) (hcont ω) (G ω)).mpr (hGspec ω hex)
  have hGuniq : ∀ (ω : Ω) (w : ℂ), Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) →
      (∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c)) → G ω = w := by
    intro ω w hw hex
    have hrat : Tendsto (fun q => F q ω) ratFilter (𝓝 w) :=
      (tendsto_nhdsWithin_zero_iff_rat (f ω) (hcont ω) w).mp hw
    have hlim : Tendsto (fun q => F q ω) ratFilter (𝓝 (G ω)) := hGspec ω hex
    exact tendsto_nhds_unique hlim hrat
  -- refined measurable test sets
  have hGim : Measurable (fun ω => (G ω).im) :=
    Complex.continuous_im.measurable.comp hGmeas
  have hpos_meas : MeasurableSet { ω : Ω | 0 < (G ω).im } :=
    measurableSet_lt measurable_const hGim
  have hzero_meas : MeasurableSet { ω : Ω | (G ω).im = 0 } :=
    measurableSet_eq_fun hGim measurable_const
  have hne_meas : MeasurableSet { ω : Ω | G ω ≠ 0 } := by
    have hEq : MeasurableSet { ω : Ω | G ω = 0 } :=
      measurableSet_eq_fun hGmeas measurable_const
    have hcompl : { ω : Ω | G ω ≠ 0 } = { ω : Ω | G ω = 0 }ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ne_eq]
    rw [hcompl]
    exact hEq.compl
  -- positivity event
  have hpos_eq : { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ 0 < w.im } =
      { ω : Ω | ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) } ∩ { ω : Ω | 0 < (G ω).im } := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, hw, hpos⟩
      have hex : ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) := (hiff ω).mp ⟨w, hw⟩
      refine ⟨hex, ?_⟩
      have hGw : G ω = w := hGuniq ω w hw hex
      rw [hGw]
      exact hpos
    · rintro ⟨hex, hpos⟩
      refine ⟨G ω, hGfull ω hex, hpos⟩
  have hpos : MeasurableSet { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ 0 < w.im } := by
    rw [hpos_eq]
    exact hEcnt.inter hpos_meas
  -- zero-imaginary event
  have hzero_eq : { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ w.im = 0 } =
      { ω : Ω | ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) } ∩ { ω : Ω | (G ω).im = 0 } := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, hw, hzero⟩
      have hex : ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) := (hiff ω).mp ⟨w, hw⟩
      refine ⟨hex, ?_⟩
      have hGw : G ω = w := hGuniq ω w hw hex
      rw [hGw]
      exact hzero
    · rintro ⟨hex, hzero⟩
      exact ⟨G ω, hGfull ω hex, hzero⟩
  have hzero : MeasurableSet { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ w.im = 0 } := by
    rw [hzero_eq]
    exact hEcnt.inter hzero_meas
  -- nonzero-limit event
  have hne_eq : { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ w ≠ 0 } =
      { ω : Ω | ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) } ∩ { ω : Ω | G ω ≠ 0 } := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, hw, hne⟩
      have hex : ∃ c : ℂ, Tendsto (fun q => F q ω) ratFilter (𝓝 c) := (hiff ω).mp ⟨w, hw⟩
      refine ⟨hex, ?_⟩
      have hGw : G ω = w := hGuniq ω w hw hex
      rw [hGw]
      exact hne
    · rintro ⟨hex, hne⟩
      exact ⟨G ω, hGfull ω hex, hne⟩
  have hne : MeasurableSet { ω : Ω | ∃ w : ℂ, Tendsto (f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 w) ∧ w ≠ 0 } := by
    rw [hne_eq]
    exact hEcnt.inter hne_meas
  exact ⟨hEfull, hpos, hzero, hne⟩

end AndersonAC.SolS9Inf
