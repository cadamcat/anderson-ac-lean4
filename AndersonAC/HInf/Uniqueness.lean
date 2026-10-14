import AndersonAC.HInf.PoissonJensen

open MeasureTheory Filter Topology Complex Real Set Metric

namespace AndersonAC.LunaHinf

def upper : Set ℂ := {z | 0 < z.im}

theorem zeroSet_countable {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upper)
    (hne : ∃ z : ℂ, 0 < z.im ∧ f z ≠ 0) :
    {z : ℂ | 0 < z.im ∧ f z = 0}.Countable := by
  obtain ⟨z₀, hz₀, hfz₀⟩ := hne
  have hopen : IsOpen upper := isOpen_lt continuous_const continuous_im
  have hfa : AnalyticOnNhd ℂ f upper := hf.analyticOnNhd hopen
  have hconn : IsConnected upper :=
    (convex_halfSpace_im_gt (0 : ℝ)).isConnected ⟨I, by simp⟩
  have hnonzero : f ⁻¹' ({0}ᶜ) ∈ codiscreteWithin upper :=
    hfa.preimage_zero_mem_codiscreteWithin hfz₀ hz₀ hconn
  let Z : Set ℂ := {z | z ∈ upper ∧ f z = 0}
  have hdisc : IsDiscrete Z := by
    rw [isDiscrete_iff_nhdsNE]
    intro z hz
    have h := (mem_codiscreteWithin.mp hnonzero) z hz.1
    have hset : upper \ (f ⁻¹' ({0}ᶜ)) = Z := by
      ext w
      simp [Z, upper]
    rw [hset] at h
    exact disjoint_iff.mp h
  have hcount : Z.Countable :=
    (HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete hdisc
  have heq : {z : ℂ | 0 < z.im ∧ f z = 0} = Z := by
    ext z
    simp [Z, upper]
  rw [heq]
  exact hcount

theorem exists_regular_height (bad : Set ℝ) (hbad : bad.Countable)
    {δ : ℝ} (hδ : 0 < δ) : ∃ η ∈ Ioo 0 δ, η ∉ bad := by
  have hpos : 0 < volume (Ioo 0 δ) := (Measure.measure_Ioo_pos volume).2 hδ
  have hnull : volume bad = 0 := hbad.measure_zero volume
  by_contra h
  push_neg at h
  have hsub : Ioo 0 δ ⊆ bad := fun η hη => h η hη
  have hle : volume (Ioo 0 δ) ≤ volume bad := measure_mono hsub
  rw [hnull] at hle
  exact (not_le_of_gt hpos) hle

noncomputable def regularHeights (bad : Set ℝ) (hbad : bad.Countable)
    (y₀ : ℝ) (hy₀ : 0 < y₀) : ℕ → ℝ := fun n =>
  Classical.choose (exists_regular_height bad hbad
    (δ := min (y₀ / 2) (1 / ((n : ℝ) + 1))) (by positivity))

theorem regularHeights_spec (bad : Set ℝ) (hbad : bad.Countable)
    (y₀ : ℝ) (hy₀ : 0 < y₀) (n : ℕ) :
    regularHeights bad hbad y₀ hy₀ n ∈ Ioo 0 (min (y₀ / 2) (1 / ((n : ℝ) + 1))) ∧
      regularHeights bad hbad y₀ hy₀ n ∉ bad := by
  exact Classical.choose_spec (exists_regular_height bad hbad
    (δ := min (y₀ / 2) (1 / ((n : ℝ) + 1))) (by positivity))

theorem tendsto_regularHeights_zero (bad : Set ℝ) (hbad : bad.Countable)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    Tendsto (regularHeights bad hbad y₀ hy₀) atTop (𝓝 0) := by
  have hrec : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrec
  · intro n
    exact le_of_lt (regularHeights_spec bad hbad y₀ hy₀ n).1.1
  · intro n
    exact le_trans (le_of_lt (regularHeights_spec bad hbad y₀ hy₀ n).1.2)
      (min_le_right _ _)

theorem diskBoundaryX_surjective {x₀ a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∃ θ ∈ Ioc 0 (2 * π), θ ≠ 2 * π ∧ diskBoundaryX x₀ a θ = x := by
  let t : ℝ := x - x₀
  let w : ℂ := ((t : ℂ) - (a : ℂ) * I) / ((t : ℂ) + (a : ℂ) * I)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hden : (t : ℂ) + (a : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ha.ne' this
  have hnumNorm : ‖(t : ℂ) - (a : ℂ) * I‖ = ‖(t : ℂ) + (a : ℂ) * I‖ := by
    have hleft : ‖(t : ℂ) - (a : ℂ) * I‖ = Real.sqrt (t ^ 2 + a ^ 2) := by
      rw [show (t : ℂ) - (a : ℂ) * I = (t : ℂ) + (-a : ℝ) * I by push_cast; ring,
        Complex.norm_add_mul_I]
      congr 1
      ring
    have hright : ‖(t : ℂ) + (a : ℂ) * I‖ = Real.sqrt (t ^ 2 + a ^ 2) := by
      rw [Complex.norm_add_mul_I]
    rw [hleft, hright]
  have hw : ‖w‖ = 1 := by
    simp [w, Complex.norm_div, hnumNorm, hden]
  have hw1 : w ≠ 1 := by
    intro h
    have hmul := (div_eq_iff hden).mp (by simpa [w] using h)
    have him := congrArg Complex.im hmul
    simp at him
    linarith
  have hwmem : w ∈ sphere 0 |(1 : ℝ)| := by
    simpa [mem_sphere, dist_eq_norm] using hw
  have hwrange : w ∈ circleMap 0 1 '' Ioc 0 (2 * π) := by
    simpa only [image_circleMap_Ioc] using hwmem
  obtain ⟨θ, hθ, hθw⟩ := hwrange
  have hθne : θ ≠ 2 * π := by
    intro h
    rw [h] at hθw
    have h2pi : circleMap 0 1 (2 * π) = 1 := by
      have hp := (periodic_circleMap 0 1) 0
      have h0 : circleMap 0 1 0 = 1 := by simp [circleMap]
      simpa only [zero_add] using hp.trans h0
    rw [h2pi] at hθw
    exact hw1 hθw.symm
  have hratio : (1 + w) / (1 - w) = (-t / a : ℝ) * I := by
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
    rw [div_eq_iff h1w]
    dsimp [w]
    field_simp [hden, haC]
    push_cast
    have hI : (I : ℂ) ^ 2 = -1 := by norm_num
    field_simp [haC]
    ring_nf
    rw [hI]
    ring
  have hmap : diskUpper x₀ 0 a w = (x : ℂ) := by
    simp only [diskUpper]
    rw [hratio]
    push_cast
    have hI : (I : ℂ) ^ 2 = -1 := by norm_num
    field_simp [haC]
    ring_nf
    rw [hI]
    simp [t]
  have hval : diskBoundaryX x₀ a θ = x := by
    change (diskUpper x₀ 0 a (circleMap 0 1 θ)).re = x
    rw [hθw, hmap]
    simp
  exact ⟨θ, hθ, hθne, hval⟩

end AndersonAC.LunaHinf

namespace AndersonAC.HInf

open AndersonAC.LunaHinf

theorem volume_boundaryZero_eq_zero (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hbdd : ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ M)
    (hne : ∃ z : ℂ, 0 < z.im ∧ f z ≠ 0) :
    volume {x : ℝ | Tendsto (fun η : ℝ => f ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 0)} = 0 := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨z₀, hz₀, hfz₀⟩ := hne
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hfz₀) (hM z₀ hz₀)
  let g : ℂ → ℂ := fun z => f z / (M : ℂ)
  have hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := by
    exact hf.div_const (M : ℂ)
  have hgbdd : ∀ z : ℂ, 0 < z.im → ‖g z‖ ≤ 1 := by
    intro z hz
    have hnorm : ‖g z‖ = ‖f z‖ / M := by
      simp [g, norm_div, norm_real, abs_of_pos hMpos]
    rw [hnorm]
    exact (div_le_one hMpos).2 (hM z hz)
  have hgne : ∃ z : ℂ, 0 < z.im ∧ g z ≠ 0 := by
    refine ⟨z₀, hz₀, ?_⟩
    simp [g, hfz₀, hMpos.ne']
  let zeros : Set ℂ := {z | 0 < z.im ∧ f z = 0}
  have hzeros : zeros.Countable := by
    simpa [zeros, AndersonAC.LunaHinf.upper] using
      AndersonAC.LunaHinf.zeroSet_countable hf ⟨z₀, hz₀, hfz₀⟩
  let bad : Set ℝ := Complex.im '' zeros
  have hbad : bad.Countable := hzeros.image Complex.im
  let x₀ : ℝ := z₀.re
  let a : ℝ := z₀.im
  have ha : 0 < a := hz₀
  have hz₀repr : (x₀ : ℂ) + (a : ℂ) * I = z₀ := by
    simpa [x₀, a] using (re_add_im z₀)
  let η : ℕ → ℝ := regularHeights bad hbad a ha
  have hηT : Tendsto η atTop (𝓝 0) := by
    simpa [η] using tendsto_regularHeights_zero bad hbad a ha
  have hηpos (n : ℕ) : 0 < η n :=
    (regularHeights_spec bad hbad a ha n).1.1
  have hηwithin : Tendsto η atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hηT, Eventually.of_forall hηpos⟩
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hgA : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.im} := hg.analyticOnNhd hopen
  have hg0 : g z₀ ≠ 0 := by
    simp [g, hfz₀, hMpos.ne']
  let c : ℝ := ‖g z₀‖ / 2
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hbase : ‖g z₀‖ ≤ 1 := hgbdd z₀ hz₀
    linarith
  let center : ℕ → ℂ := fun n => (x₀ : ℂ) + ((η n + a : ℝ) : ℂ) * I
  have hcenterT : Tendsto center atTop (𝓝 z₀) := by
    have hcont : Continuous fun y : ℝ => (x₀ : ℂ) + ((y + a : ℝ) : ℂ) * I := by
      fun_prop
    have h := hcont.continuousAt.tendsto.comp hηT
    change Tendsto (fun n : ℕ => (x₀ : ℂ) + ((η n + a : ℝ) : ℂ) * I)
      atTop (𝓝 z₀)
    simpa [Function.comp_def, center, hz₀repr] using h
  have hnormCenter : Tendsto (fun n => ‖g (center n)‖) atTop (𝓝 ‖g z₀‖) := by
    exact continuous_norm.continuousAt.tendsto.comp
      ((hgA z₀ hz₀).continuousAt.tendsto.comp hcenterT)
  have hcenterEventually : ∀ᶠ n in atTop, c < ‖g (center n)‖ := by
    exact hnormCenter (Ioi_mem_nhds (by
      dsimp [c]
      linarith [norm_pos_iff.mpr hg0]))
  let K : ℝ := (2 * π) * (-Real.log c)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity)
      (neg_nonneg.mpr (Real.log_nonpos hcpos.le hc_le_one))
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  let q : ℕ → ℝ → ENNReal := fun n θ =>
    ENNReal.ofReal (-Real.log ‖g (diskUpper x₀ (η n) a (circleMap 0 1 θ))‖)
  have hXmeas : Measurable (diskBoundaryX x₀ a) := by
    unfold diskBoundaryX diskUpper
    fun_prop
  have hLineCont (n : ℕ) : Continuous (fun x : ℝ =>
      g ((x : ℂ) + (η n : ℂ) * I)) := by
    have hcoord : Continuous (fun x : ℝ => (x : ℂ) + (η n : ℂ) * I) := by
      fun_prop
    have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ) + (η n : ℂ) * I)
        univ {z : ℂ | 0 < z.im} := by
      intro x _
      simp [hηpos n]
    have hgCont : ContinuousOn g {z : ℂ | 0 < z.im} :=
      continuousOn_of_forall_continuousAt fun z hz => (hgA z hz).continuousAt
    exact continuousOn_univ.mp (hgCont.comp hcoord.continuousOn hmaps)
  have hqMeas : ∀ n : ℕ, AEMeasurable (q n) μ := by
    intro n
    have hcomp : Measurable (fun θ : ℝ =>
        g ((diskBoundaryX x₀ a θ : ℝ) + (η n : ℂ) * I)) :=
      (hLineCont n).measurable.comp hXmeas
    have hqeq : q n = fun θ : ℝ => ENNReal.ofReal
        (-Real.log ‖g ((diskBoundaryX x₀ a θ : ℝ) + (η n : ℂ) * I)‖) := by
      funext θ
      simp only [q, diskUpper_circleBoundary_eq]
    rw [hqeq]
    exact (ENNReal.continuous_ofReal.measurable.comp
      (measurable_neg.comp (Real.measurable_log.comp
        ((continuous_norm.measurable).comp hcomp)))).aemeasurable
  have hline (n : ℕ) (x : ℝ) :
      g ((x : ℂ) + (η n : ℂ) * I) ≠ 0 := by
    have hz : 0 < ((x : ℂ) + (η n : ℂ) * I).im := by simp [hηpos n]
    intro hzero
    have hfzero : f ((x : ℂ) + (η n : ℂ) * I) = 0 := by
      have heq := hzero
      simp [g, hMpos.ne'] at heq
      exact heq
    have hbadη : η n ∈ bad := by
      have hmem : Complex.im ((x : ℂ) + (η n : ℂ) * I) ∈ Complex.im '' zeros :=
        Set.mem_image_of_mem Complex.im ⟨hz, hfzero⟩
      simpa [bad] using hmem
    exact (regularHeights_spec bad hbad a ha n).2 hbadη
  have hJ (n : ℕ) (hn : c < ‖g (center n)‖) :
      ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal
        (-Real.log ‖g (diskUpper x₀ (η n) a (circleMap 0 1 θ))‖) ∂volume ≤
          ENNReal.ofReal K := by
    have hcenter : g (center n) ≠ 0 := norm_pos_iff.mp (lt_trans hcpos hn)
    have hJraw := halfPlane_poissonJensen_angle hg hgbdd (ha := ha)
      (hηpos n) (by simpa [center] using hcenter) (hline n)
    have hlog : -Real.log ‖g (center n)‖ ≤ -Real.log c := by
      apply neg_le_neg
      exact Real.log_le_log hcpos (le_of_lt hn)
    have hscale : (2 * π) * (-Real.log ‖g (center n)‖) ≤ K := by
      dsimp [K]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    exact le_trans hJraw (by
      simpa [center] using ENNReal.ofReal_le_ofReal hscale)
  have hIntBound : ∀ᶠ n in atTop,
      (∫⁻ θ, q n θ ∂μ) ≤ ENNReal.ofReal K := by
    filter_upwards [hcenterEventually] with n hn
    have hj := hJ n hn
    simpa [μ, q] using hj
  have hfreq : ∃ᶠ n in atTop,
      (∫⁻ θ, q n θ ∂μ) ≤ ENNReal.ofReal K := hIntBound.frequently
  let E : Set ℝ := {x | Tendsto (fun η : ℝ => f ((x : ℂ) + (η : ℂ) * I))
    (𝓝[>] 0) (𝓝 0)}
  have hEzero : volume E = 0 := by
    by_contra hE
    have hunion : E = ⋃ n : ℕ, E ∩ Icc (-(n : ℝ)) (n : ℝ) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        have hn' : |x| < (n : ℝ) := by exact_mod_cast hn
        have hbounds := abs_lt.mp hn'
        exact mem_iUnion.2 ⟨n, ⟨hx, ⟨le_of_lt hbounds.1, le_of_lt hbounds.2⟩⟩⟩
      · intro hx
        obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
        exact hxn.1
    have hex : ∃ n : ℕ, volume (E ∩ Icc (-(n : ℝ)) (n : ℝ)) ≠ 0 := by
      by_contra hpieces
      push_neg at hpieces
      have hzero : volume E = 0 := by
        rw [hunion]
        apply le_antisymm
        · calc
            volume (⋃ n : ℕ, E ∩ Icc (-(n : ℝ)) (n : ℝ)) ≤
                ∑' n : ℕ, volume (E ∩ Icc (-(n : ℝ)) (n : ℝ)) := measure_iUnion_le _
            _ = 0 := by simp [hpieces]
        · exact zero_le
      exact hE hzero
    obtain ⟨N, hBne⟩ := hex
    let B : Set ℝ := E ∩ Icc (-(N : ℝ)) (N : ℝ)
    have hBpos : 0 < volume B := by
      by_contra h
      have hz : volume B ≤ 0 := not_lt.mp h
      have : volume B = 0 := le_antisymm hz zero_le
      exact hBne (by simpa [B] using this)
    let A : Set ℝ := {θ | θ ∈ Ioc 0 (2 * π) ∧ θ ≠ 2 * π ∧ diskBoundaryX x₀ a θ ∈ B}
    have himage : diskBoundaryX x₀ a '' A = B := by
      ext x
      constructor
      · rintro ⟨θ, hθA, rfl⟩
        exact hθA.2.2
      · intro hx
        obtain ⟨θ, hθ, hθne, hθx⟩ := diskBoundaryX_surjective ha x
        refine ⟨θ, ⟨hθ, hθne, ?_⟩, hθx⟩
        rw [hθx]
        exact hx
    have hdiff : DifferentiableOn ℝ (diskBoundaryX x₀ a) A := by
      intro θ hθA
      have hcmne : circleMap 0 1 θ ≠ 1 := by
        intro heq
        have hcircle : circleMap 0 1 θ = circleMap 0 1 (2 * π) := by
          simpa [circleMap] using heq
        have hθlt : |θ - 2 * π| < 2 * π := by
          rw [abs_lt]
          constructor <;> linarith [hθA.1.1, hθA.1.2, hθA.2.1, Real.two_pi_pos]
        have heqθ := eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) hθlt hcircle
        exact hθA.2.1 heqθ
      have hden : (1 : ℂ) - circleMap 0 1 θ ≠ 0 :=
        sub_ne_zero.mpr hcmne.symm
      have hratDiff : DifferentiableAt ℝ (diskUpper x₀ 0 a) (circleMap 0 1 θ) := by
        have hnum : DifferentiableAt ℝ (fun w : ℂ => 1 + w)
            (circleMap 0 1 θ) := by fun_prop
        have hdenFun : DifferentiableAt ℝ (fun w : ℂ => 1 - w)
            (circleMap 0 1 θ) := by fun_prop
        have hquot : DifferentiableAt ℝ (fun w : ℂ => (1 + w) / (1 - w))
            (circleMap 0 1 θ) := by
          change DifferentiableAt ℝ (fun w : ℂ => (1 + w) * (1 - w)⁻¹)
            (circleMap 0 1 θ)
          exact hnum.mul (hdenFun.inv hden)
        unfold diskUpper
        have hconstA : DifferentiableAt ℝ (fun _ : ℂ => (a : ℂ) * I)
            (circleMap 0 1 θ) :=
          differentiableAt_const _
        have hconstX : DifferentiableAt ℝ
            (fun _ : ℂ => (x₀ : ℂ) + (0 : ℂ) * I)
            (circleMap 0 1 θ) := differentiableAt_const _
        have hscaled : DifferentiableAt ℝ
            (fun w : ℂ => (a : ℂ) * I * ((1 + w) / (1 - w))) (circleMap 0 1 θ) :=
          hconstA.mul hquot
        have houter : DifferentiableAt ℝ
            (fun w : ℂ => (x₀ : ℂ) + (0 : ℂ) * I +
              (a : ℂ) * I * ((1 + w) / (1 - w))) (circleMap 0 1 θ) := hconstX.add hscaled
        simpa using houter
      have hcircleDiff : DifferentiableAt ℝ (circleMap 0 1) θ :=
        (differentiable_circleMap 0 1).differentiableAt
      have hcompDiff : DifferentiableAt ℝ
          (fun u : ℝ => diskUpper x₀ 0 a (circleMap 0 1 u)) θ :=
        hratDiff.comp θ hcircleDiff
      have hreDiff : DifferentiableAt ℝ Complex.re
          (diskUpper x₀ 0 a (circleMap 0 1 θ)) :=
        Complex.differentiable_re.differentiableAt
      have hdiffAt : DifferentiableAt ℝ (diskBoundaryX x₀ a) θ := by
        change DifferentiableAt ℝ
          (fun u : ℝ => Complex.re (diskUpper x₀ 0 a (circleMap 0 1 u))) θ
        exact hreDiff.comp θ hcompDiff
      exact hdiffAt.differentiableWithinAt
    have hAne : μ A ≠ 0 := by
      intro hAzero
      have hBzero := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
        (μ := volume) hdiff (by
          have hAvol : volume A = 0 := by
            have hsub : A ⊆ Ioc 0 (2 * π) := fun _ hθ => hθ.1
            simpa [μ, Measure.restrict_apply' measurableSet_Ioc, inter_eq_left.mpr hsub] using hAzero
          exact hAvol)
      rw [himage] at hBzero
      exact (ne_of_gt hBpos) hBzero
    have hAmeas : μ A ≠ 0 := hAne
    have hqLiminf : AEMeasurable
        (fun θ => liminf (fun n => q n θ) atTop) μ := AEMeasurable.liminf hqMeas
    have hdiverge : ∀ θ ∈ A,
        liminf (fun n => q n θ) atTop = (⊤ : ENNReal) := by
      intro θ hθA
      let x : ℝ := diskBoundaryX x₀ a θ
      have hxE : x ∈ E := hθA.2.2.1
      have hlimitF : Tendsto (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I))
          (𝓝[>] 0) (𝓝 0) := hxE
      have hlimitSeqF : Tendsto (fun n : ℕ =>
          f ((x : ℂ) + (η n : ℂ) * I)) atTop (𝓝 0) := hlimitF.comp hηwithin
      have hdivCont : ContinuousAt (fun z : ℂ => z / (M : ℂ)) 0 := by
        fun_prop
      have hlimitG : Tendsto (fun n : ℕ =>
          g ((x : ℂ) + (η n : ℂ) * I)) atTop (𝓝 0) := by
        have h := hdivCont.tendsto.comp hlimitSeqF
        simpa [Function.comp_def, g] using h
      have hnormT : Tendsto (fun n : ℕ =>
          ‖g ((x : ℂ) + (η n : ℂ) * I)‖) atTop (𝓝 0) :=
        by simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp hlimitG
      have hlineNe : ∀ n, g ((x : ℂ) + (η n : ℂ) * I) ≠ 0 := fun n => hline n x
      have hnormWithin : Tendsto
          (fun n : ℕ => ‖g ((x : ℂ) + (η n : ℂ) * I)‖) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hnormT, Eventually.of_forall (fun n => norm_pos_iff.mpr (hlineNe n))⟩
      have hlog : Tendsto (fun n : ℕ =>
          -Real.log ‖g ((x : ℂ) + (η n : ℂ) * I)‖) atTop atTop := by
        simpa [Function.comp_def] using
          tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hnormWithin)
      have hqT : Tendsto (fun n : ℕ => ENNReal.ofReal
          (-Real.log ‖g ((x : ℂ) + (η n : ℂ) * I)‖)) atTop (𝓝 (⊤ : ENNReal)) := by
        exact ENNReal.tendsto_ofReal_atTop.comp hlog
      have hqeq : ∀ n, q n θ = ENNReal.ofReal
          (-Real.log ‖g ((x : ℂ) + (η n : ℂ) * I)‖) := by
        intro n
        dsimp [q, x]
        rw [diskUpper_circleBoundary_eq]
      have hqT' : Tendsto (fun n => q n θ) atTop (𝓝 (⊤ : ENNReal)) := by
        exact hqT.congr' (Eventually.of_forall fun n => (hqeq n).symm)
      exact hqT'.liminf_eq
    have htopset : NullMeasurableSet
        {θ | liminf (fun n => q n θ) atTop = (⊤ : ENNReal)} μ :=
      hqLiminf.nullMeasurableSet_preimage (measurableSet_singleton ⊤)
    have htopmeasure : μ {θ | liminf (fun n => q n θ) atTop = (⊤ : ENNReal)} ≠ 0 := by
      intro hz
      have hsubset : A ⊆ {θ | liminf (fun n => q n θ) atTop = (⊤ : ENNReal)} := by
        intro θ hθ
        exact hdiverge θ hθ
      have hAle : μ A ≤ 0 := by
        calc
          μ A ≤ μ {θ | liminf (fun n => q n θ) atTop = (⊤ : ENNReal)} := measure_mono hsubset
          _ = 0 := hz
      exact hAmeas (le_antisymm hAle zero_le)
    have hlimTop : ∫⁻ θ, liminf (fun n => q n θ) atTop ∂μ = (⊤ : ENNReal) :=
      lintegral_eq_top_of_measure_eq_top_ne_zero hqLiminf htopmeasure
    have hfatou : (∫⁻ θ, liminf (fun n => q n θ) atTop ∂μ) ≤
        liminf (fun n => ∫⁻ θ, q n θ ∂μ) atTop := lintegral_liminf_le' hqMeas
    have hlimInt : liminf (fun n => ∫⁻ θ, q n θ ∂μ) atTop ≤ ENNReal.ofReal K := by
      apply liminf_le_of_frequently_le'
      exact hfreq
    have htople : (⊤ : ENNReal) ≤ ENNReal.ofReal K := by
      rw [← hlimTop]
      exact hfatou.trans hlimInt
    exact (not_le_of_gt ENNReal.ofReal_lt_top) htople
  simpa [E] using hEzero

end AndersonAC.HInf
