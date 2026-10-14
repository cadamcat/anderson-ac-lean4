import AndersonAC.AgentS78.Construction.ClearingTrialReindex
import AndersonAC.S2.SignResampling
import AndersonAC.S2.BinaryDecoder

/-!
# the residual law of the clearing trial

07-assembly.tex:200–236 ("The true residual at a selected pivot"): the pivot of a running
heat is predictable and distinct from the earlier pivots, so every event of the trial's
query history on `{k < stop, pivot k = y}` is unchanged when the true signs of site `y` are
flipped. Under the product law of the signs (sign flips preserve `sourcesLaw`,
`SolS2.signFlip_law`) the revealed residual is therefore centered with conditional second
moment `λ² 4^{-h} / 3` (02-state.tex:85–89).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.Residual

open AndersonAC.S6

/-! ## Saturated events of a query history -/

/-- Sets that do not separate `ω` and `ω'`. -/
def satSpace {Ω : Type} (ω ω' : Ω) : MeasurableSpace Ω where
  MeasurableSet' s := (ω ∈ s ↔ ω' ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl s h := by
    simp only [Set.mem_compl_iff]
    exact not_congr h
  measurableSet_iUnion f hf := by
    simp only [Set.mem_iUnion]
    exact exists_congr hf

theorem queryHistory_sat {Ω ι : Type} [MeasurableSpace ι] (pivot : ℕ → Ω → ι)
    (residual : ℕ → Ω → ℝ) (k : ℕ) (ω ω' : Ω)
    (h : ∀ j < k, pivot j ω = pivot j ω' ∧ residual j ω = residual j ω') :
    queryHistory ⊥ pivot residual k ≤ satSpace ω ω' := by
  unfold queryHistory
  refine sup_le bot_le (iSup₂_le fun j hj => sup_le ?_ ?_)
  · intro s hs
    obtain ⟨A, -, rfl⟩ := hs
    show (ω ∈ pivot j ⁻¹' A ↔ ω' ∈ pivot j ⁻¹' A)
    simp only [Set.mem_preimage, (h j (Finset.mem_range.mp hj)).1]
  · intro s hs
    obtain ⟨A, -, rfl⟩ := hs
    show (ω ∈ residual j ⁻¹' A ↔ ω' ∈ residual j ⁻¹' A)
    simp only [Set.mem_preimage, (h j (Finset.mem_range.mp hj)).2]

/-! ## Pivots of a running trial are distinct -/

section Trial

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

theorem pivot_not_active (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) :
    ∀ i j, j < i → i ≤ q.stop ω → q.pivot j ω ∉ (q.state i ω).active := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj hi
    obtain ⟨-, -, hact, -⟩ := q.heat i ω (by omega)
    rw [hact, Finset.mem_erase, not_and_or, not_not]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact Or.inr (ih j hj (by omega))
    · exact Or.inl (hj ▸ rfl)

theorem pivot_ne (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) {j k : ℕ}
    (hjk : j < k) (hk : k < q.stop ω) : q.pivot j ω ≠ q.pivot k ω := by
  intro h
  obtain ⟨hx, -⟩ := q.heat k ω hk
  exact pivot_not_active q ω k j hjk hk.le (h ▸ hx)

/-- A map that fixes the true residual of every site but `y` fixes the history of a running
trial whose pivots avoid `y`. -/
theorem history_agree (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hhist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k)
    (R : ι → Ω → ℝ) (hres : ∀ k ω, k < q.stop ω → q.residual k ω = R (q.pivot k ω) ω)
    (y : ι) (F : Ω → Ω) (hF : ∀ i, i ≠ y → ∀ ω, R i (F ω) = R i ω) :
    ∀ k ω, (∀ j < k, j < q.stop ω ∧ q.pivot j ω ≠ y) →
      ∀ j < k, q.pivot j (F ω) = q.pivot j ω ∧ q.residual j (F ω) = q.residual j ω ∧
        j < q.stop (F ω) := by
  intro k
  induction k with
  | zero => intro ω _ j hj; omega
  | succ k ih =>
    intro ω hω j hj
    have hprev := ih ω (fun j hj => hω j (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hprev j hj
    have hsat : q.history j ≤ satSpace ω (F ω) := by
      rw [hhist j]
      exact queryHistory_sat _ _ j ω (F ω)
        (fun i hi => ⟨(hprev i hi).1.symm, (hprev i hi).2.1.symm⟩)
    have hpiv : q.pivot j (F ω) = q.pivot j ω := by
      have hm : MeasurableSet[q.history j] (q.pivot j ⁻¹' {q.pivot j ω}) :=
        q.pivot_predictable j (measurableSet_singleton _)
      have := (hsat _ hm).mp rfl
      exact this
    have hstop : j < q.stop (F ω) := by
      have hm : MeasurableSet[q.history j] {ω | ((q.stop ω : ℕ) : WithTop ℕ) ≤ (j : WithTop ℕ)} :=
        q.stopping j
      have h1 := hsat _ hm
      have h2 : ¬ ((q.stop ω : WithTop ℕ) ≤ (j : WithTop ℕ)) := by
        exact_mod_cast (not_le.mpr (hω j hj).1)
      have h3 : ¬ ((q.stop (F ω) : WithTop ℕ) ≤ (j : WithTop ℕ)) := fun h => h2 (h1.mpr h)
      have h4 : ¬ q.stop (F ω) ≤ j := by exact_mod_cast h3
      omega
    refine ⟨hpiv, ?_, hstop⟩
    rw [hres j (F ω) hstop, hres j ω (hω j hj).1, hpiv]
    exact hF _ (hω j hj).2 ω

/-- Events of the history on `{k < stop, pivot k = y}` are invariant under such maps. -/
theorem event_invariant (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hhist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k)
    (R : ι → Ω → ℝ) (hres : ∀ k ω, k < q.stop ω → q.residual k ω = R (q.pivot k ω) ω)
    (y : ι) (F : Ω → Ω) (hF : ∀ i, i ≠ y → ∀ ω, R i (F ω) = R i ω)
    (k : ℕ) (E : Set Ω) (hE : MeasurableSet[q.history k] E) (ω : Ω)
    (hk : k < q.stop ω) (hy : q.pivot k ω = y) : F ω ∈ E ↔ ω ∈ E := by
  have hω : ∀ j < k, j < q.stop ω ∧ q.pivot j ω ≠ y :=
    fun j hj => ⟨by omega, hy ▸ pivot_ne q ω hj hk⟩
  have hagree := history_agree q hhist R hres y F hF k ω hω
  have hsat : q.history k ≤ satSpace ω (F ω) := by
    rw [hhist k]
    exact queryHistory_sat _ _ k ω (F ω)
      (fun i hi => ⟨(hagree i hi).1.symm, (hagree i hi).2.1.symm⟩)
  exact (hsat E hE).symm

end Trial

/-! ## Moments of a site suffix on flip-invariant events -/

section Moments

open AndersonAC.S2 AndersonAC.SolS2

variable (S : Type) [Fintype S] [DecidableEq S] {M : ℕ → ℕ}

/-- The true signs of site `y`. -/
def siteDigits (y : S) (ω : RandomSources S M) : ℕ → Bool := fun n => ω.1 (Sum.inl (y, n))

/-- The `λ`-coupled suffix of site `y` from height `h`. -/
def siteSuffix (lam : ℝ) (h : ℕ) (y : S) (ω : RandomSources S M) : ℝ :=
  binarySuffix lam h (siteDigits S y ω)

/-- The sign indices of site `y`. -/
def siteMask (y : S) : Set (SignIndex S) := {a | ∃ n, a = Sum.inl (y, n)}

theorem siteDigits_measurable (y : S) : Measurable (siteDigits (M := M) S y) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_pi_apply _).comp measurable_fst

theorem siteSuffix_measurable (lam : ℝ) (h : ℕ) (y : S) :
    Measurable (siteSuffix (M := M) S lam h y) :=
  (binarySuffix_measurable lam h).comp (siteDigits_measurable S y)

theorem siteSuffix_bound (lam : ℝ) (h : ℕ) (y : S) (ω : RandomSources S M) :
    |siteSuffix S lam h y ω| ≤ |lam| / 2 ^ h :=
  binarySuffix_bound lam h _

theorem siteDigits_flip_other {mask : Set (SignIndex S)} {y y' : S} (hmask : mask ⊆ siteMask S y)
    (hy : y' ≠ y) (ω : RandomSources S M) :
    siteDigits S y' (signFlip S mask ω) = siteDigits S y' ω := by
  funext n
  have : (Sum.inl (y', n) : SignIndex S) ∉ mask := by
    intro h
    obtain ⟨m, hm⟩ := hmask h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at hm
    exact hy hm.1
  simp [siteDigits, signFlip, flipSigns, this]

theorem integral_signFlip (mask : Set (SignIndex S)) (G : RandomSources S M → ℝ)
    (hG : Measurable G) :
    ∫ ω, G (signFlip S mask ω) ∂sourcesLaw S M = ∫ ω, G ω ∂sourcesLaw S M := by
  conv_rhs => rw [← signFlip_law S mask]
  rw [integral_map (signFlip_measurable S mask).aemeasurable hG.aestronglyMeasurable]

theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> simp [signValue]

theorem binarySuffix_not (lam : ℝ) (h : ℕ) (a : ℕ → Bool) :
    binarySuffix lam h (fun n => !a n) = -binarySuffix lam h a := by
  unfold binarySuffix
  rw [← tsum_neg]
  congr 1
  funext k
  rw [signValue_not]
  ring

theorem integrable_of_bounded {G : RandomSources S M → ℝ} (hG : Measurable G) (C : ℝ)
    (hC : ∀ ω, |G ω| ≤ C) : Integrable G (sourcesLaw S M) :=
  Integrable.of_bound hG.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hC ω)

variable {S}

/-- (A) the suffix is centered on flip-invariant events. -/
theorem integral_indicator_siteSuffix (lam : ℝ) (h : ℕ) (y : S) (E : Set (RandomSources S M))
    (hE : MeasurableSet E) (hinv : ∀ ω, signFlip S (siteMask S y) ω ∈ E ↔ ω ∈ E) :
    ∫ ω, E.indicator (siteSuffix S lam h y) ω ∂sourcesLaw S M = 0 := by
  have hmeas : Measurable (E.indicator (siteSuffix (M := M) S lam h y)) :=
    (siteSuffix_measurable S lam h y).indicator hE
  have hflip := integral_signFlip S (siteMask S y) _ hmeas
  have hpt : ∀ ω, E.indicator (siteSuffix S lam h y) (signFlip S (siteMask S y) ω) =
      -E.indicator (siteSuffix S lam h y) ω := by
    intro ω
    have hd : siteDigits S y (signFlip S (siteMask S y) ω) = fun n => !siteDigits S y ω n := by
      funext n
      have : (Sum.inl (y, n) : SignIndex S) ∈ siteMask S y := ⟨n, rfl⟩
      simp [siteDigits, signFlip, flipSigns, this]
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem ((hinv ω).mpr hω), Set.indicator_of_mem hω, siteSuffix, hd,
        binarySuffix_not]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hω ((hinv ω).mp h)), Set.indicator_of_notMem hω,
        neg_zero]
  simp_rw [hpt, integral_neg] at hflip
  linarith

theorem signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by
  cases b <;> simp [signValue]

theorem integrable_indicator_bounded {G : RandomSources S M → ℝ} (hG : Measurable G) (C : ℝ)
    (hC : ∀ ω, |G ω| ≤ C) (E : Set (RandomSources S M)) (hE : MeasurableSet E) :
    Integrable (E.indicator G) (sourcesLaw S M) :=
  (integrable_of_bounded S hG C hC).indicator hE

/-- One digit of the second moment on flip-invariant events. -/
theorem integral_indicator_sq_step (lam : ℝ) (n : ℕ) (y : S) (E : Set (RandomSources S M))
    (hE : MeasurableSet E)
    (hinv : ∀ ω, signFlip S {Sum.inl (y, n)} ω ∈ E ↔ ω ∈ E) :
    ∫ ω, E.indicator (fun ω => siteSuffix S lam n y ω ^ 2) ω ∂sourcesLaw S M =
      (lam / 2 ^ (n + 1)) ^ 2 * (sourcesLaw S M).real E +
        ∫ ω, E.indicator (fun ω => siteSuffix S lam (n + 1) y ω ^ 2) ω ∂sourcesLaw S M := by
  set c := lam / (2 : ℝ) ^ (n + 1)
  let sgn : RandomSources S M → ℝ := fun ω => signValue (siteDigits S y ω n)
  let D : RandomSources S M → ℝ := fun ω => sgn ω * siteSuffix S lam (n + 1) y ω
  have hsgn : Measurable sgn :=
    (measurable_of_finite signValue).comp ((measurable_pi_apply n).comp (siteDigits_measurable S y))
  have hX' := siteSuffix_measurable (M := M) S lam (n + 1) y
  have hD : Measurable D := hsgn.mul hX'
  -- the cross term vanishes
  have hcross : ∫ ω, E.indicator D ω ∂sourcesLaw S M = 0 := by
    have hflip := integral_signFlip S {Sum.inl (y, n)} _ (hD.indicator hE)
    have hpt : ∀ ω, E.indicator D (signFlip S {Sum.inl (y, n)} ω) = -E.indicator D ω := by
      intro ω
      have hd1 : siteDigits S y (signFlip S {Sum.inl (y, n)} ω) n = !siteDigits S y ω n := by
        simp [siteDigits, signFlip, flipSigns]
      have hd2 : siteSuffix S lam (n + 1) y (signFlip S {Sum.inl (y, n)} ω) =
          siteSuffix S lam (n + 1) y ω := by
        unfold siteSuffix binarySuffix
        apply tsum_congr
        intro k
        have hne : n + 1 + k ≠ n := by omega
        simp [siteDigits, signFlip, flipSigns, hne]
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem ((hinv ω).mpr hω), Set.indicator_of_mem hω]
        simp only [D, sgn, hd1, hd2, signValue_not]
        ring
      · rw [Set.indicator_of_notMem (fun h => hω ((hinv ω).mp h)), Set.indicator_of_notMem hω,
          neg_zero]
    simp_rw [hpt, integral_neg] at hflip
    linarith
  have hpt : E.indicator (fun ω => siteSuffix S lam n y ω ^ 2) = fun ω =>
      c ^ 2 * E.indicator (fun _ => (1 : ℝ)) ω + 2 * c * E.indicator D ω +
        E.indicator (fun ω => siteSuffix S lam (n + 1) y ω ^ 2) ω := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω, D, sgn]
      rw [siteSuffix, AndersonAC.SolS2.binarySuffix_succ]
      have hsq := signValue_sq (siteDigits S y ω n)
      unfold siteSuffix
      linear_combination c ^ 2 * hsq
    · simp [Set.indicator_of_notMem hω]
  have hb : ∀ k (ω : RandomSources S M), |siteSuffix S lam k y ω ^ 2| ≤ (|lam| / 2 ^ k) ^ 2 := by
    intro k ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (siteSuffix_bound S lam k y ω) 2
  have hI1 : Integrable (E.indicator (fun _ => (1 : ℝ))) (sourcesLaw S M) :=
    integrable_indicator_bounded measurable_const 1 (by simp) E hE
  have hI2 : Integrable (E.indicator D) (sourcesLaw S M) := by
    refine integrable_indicator_bounded hD (|lam| / 2 ^ (n + 1)) (fun ω => ?_) E hE
    simp only [D, sgn, abs_mul]
    have h1 : |signValue (siteDigits S y ω n)| = 1 := by
      cases siteDigits S y ω n <;> simp [signValue]
    rw [h1, one_mul]
    exact siteSuffix_bound S lam (n + 1) y ω
  have hI3 : Integrable (E.indicator (fun ω => siteSuffix S lam (n + 1) y ω ^ 2))
      (sourcesLaw S M) :=
    integrable_indicator_bounded (hX'.pow_const 2) _ (hb (n + 1)) E hE
  rw [hpt]
  beta_reduce
  have h1 := integral_add ((hI1.const_mul (c ^ 2)).add (hI2.const_mul (2 * c))) hI3
  have h2 := integral_add (hI1.const_mul (c ^ 2)) (hI2.const_mul (2 * c))
  simp only [Pi.add_apply] at h1 h2
  have h3 : ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂sourcesLaw S M = (sourcesLaw S M).real E :=
    integral_indicator_one hE
  rw [h1, h2, integral_const_mul, integral_const_mul, hcross, h3]
  ring

theorem hasSum_suffix_variance (lam : ℝ) (h : ℕ) :
    HasSum (fun i : ℕ => (lam / 2 ^ (h + i + 1)) ^ 2) (lam ^ 2 / (3 * 4 ^ h)) := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (lam ^ 2 / 4 ^ (h + 1))
  have h2 : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
    intro k; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  convert hg using 1
  · funext i
    rw [div_pow, h2]
    simp only [one_div, inv_pow]
    field_simp
    ring
  · field_simp
    ring

/-- (B) the second moment of the suffix on events invariant under every single-digit flip. -/
theorem integral_indicator_siteSuffix_sq (lam : ℝ) (h : ℕ) (y : S) (E : Set (RandomSources S M))
    (hE : MeasurableSet E)
    (hinv : ∀ n ω, signFlip S {Sum.inl (y, n)} ω ∈ E ↔ ω ∈ E) :
    ∫ ω, E.indicator (fun ω => siteSuffix S lam h y ω ^ 2) ω ∂sourcesLaw S M =
      lam ^ 2 / (3 * 4 ^ h) * (sourcesLaw S M).real E := by
  set A := ∫ ω, E.indicator (fun ω => siteSuffix S lam h y ω ^ 2) ω ∂sourcesLaw S M
  set m := (sourcesLaw S M).real E
  let f : ℕ → ℝ := fun N =>
    ∫ ω, E.indicator (fun ω => siteSuffix S lam (h + N) y ω ^ 2) ω ∂sourcesLaw S M
  have iter : ∀ N, A = (∑ i ∈ Finset.range N, (lam / 2 ^ (h + i + 1)) ^ 2) * m + f N := by
    intro N
    induction N with
    | zero => simp [f, A]
    | succ N ih =>
      rw [ih, Finset.sum_range_succ]
      have := integral_indicator_sq_step lam (h + N) y E hE (hinv (h + N))
      simp only [f] at this ⊢
      rw [this, show h + N + 1 = h + (N + 1) by omega]
      ring
  have hbound : ∀ N, |f N| ≤ (|lam| / 2 ^ (h + N)) ^ 2 := by
    intro N
    have := norm_integral_le_of_norm_le_const (μ := sourcesLaw S M)
      (f := E.indicator (fun ω => siteSuffix S lam (h + N) y ω ^ 2))
      (C := (|lam| / 2 ^ (h + N)) ^ 2) (Eventually.of_forall fun ω => by
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (siteSuffix_bound S lam (h + N) y ω) 2
        · rw [Set.indicator_of_notMem hω, norm_zero]; positivity)
    simpa [Real.norm_eq_abs] using this
  have hS := (hasSum_suffix_variance lam h).tendsto_sum_nat
  have hf1 : Tendsto f atTop (𝓝 (A - lam ^ 2 / (3 * 4 ^ h) * m)) := by
    have : f = fun N => A - (∑ i ∈ Finset.range N, (lam / 2 ^ (h + i + 1)) ^ 2) * m := by
      funext N; rw [iter N]; ring
    rw [this]
    exact tendsto_const_nhds.sub (hS.mul_const m)
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => (hbound N).trans_eq' (Real.norm_eq_abs _))
    have : Tendsto (fun N : ℕ => (|lam| / 2 ^ h) ^ 2 * ((1 / 4 : ℝ) ^ N)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).const_mul ((|lam| / 2 ^ h) ^ 2)
    convert this using 1
    funext N
    have h2 : ((2 : ℝ) ^ N) ^ 2 = 4 ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [pow_add, div_mul_eq_div_div, div_pow (|lam| / 2 ^ h), h2]
    simp only [one_div, inv_pow]
    field_simp
  have := tendsto_nhds_unique hf1 hf0
  linarith

end Moments

/-! ## The residual law of a running trial whose residuals are site suffixes -/

section TrialLaw

open AndersonAC.S2 AndersonAC.SolS2

variable {S : Type} [Fintype S] [DecidableEq S] {M : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {core : Finset ι} {t : ℝ} {r : RandomSources S M → ι → ℂ}
  {g0 : RandomSources S M → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}

/-- The trial reveals, at a running heat, the suffix of its pivot's site. -/
structure LawHyp (q : StoppedTrial (Ω := RandomSources S M) core t r g0 order) (v : ι → S)
    (lam : ℝ) (hgt : ι → ℕ) : Prop where
  hist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k
  inj : Function.Injective v
  res : ∀ k ω, k < q.stop ω →
    q.residual k ω = siteSuffix S lam (hgt (q.pivot k ω)) (v (q.pivot k ω)) ω

variable {q : StoppedTrial (Ω := RandomSources S M) core t r g0 order} {v : ι → S} {lam : ℝ}
  {hgt : ι → ℕ}

/-- The piece of a history event on `{k < stop, pivot k = y}`. -/
def piece (q : StoppedTrial (Ω := RandomSources S M) core t r g0 order) (k : ℕ)
    (s : Set (RandomSources S M)) (y : ι) : Set (RandomSources S M) :=
  s ∩ {ω | k < q.stop ω} ∩ q.pivot k ⁻¹' {y}

theorem piece_measurable (k : ℕ) {s : Set (RandomSources S M)} (hs : MeasurableSet[q.history k] s)
    (y : ι) : MeasurableSet[q.history k] (piece q k s y) :=
  (hs.inter (stopping_lt_measurableSet q k)).inter (q.pivot_predictable k (measurableSet_singleton y))

theorem piece_inv (hq : LawHyp q v lam hgt) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) (y : ι) {mask : Set (SignIndex S)}
    (hmask : mask ⊆ siteMask S (v y)) (ω : RandomSources S M) :
    signFlip S mask ω ∈ piece q k s y ↔ ω ∈ piece q k s y := by
  let R : ι → RandomSources S M → ℝ := fun i ω => siteSuffix S lam (hgt i) (v i) ω
  have hF : ∀ i, i ≠ y → ∀ ω, R i (signFlip S mask ω) = R i ω := by
    intro i hi ω
    simp only [R, siteSuffix]
    rw [siteDigits_flip_other S hmask (hq.inj.ne hi)]
  have key : ∀ ω, ω ∈ piece q k s y → (signFlip S mask ω ∈ piece q k s y ↔ ω ∈ piece q k s y) :=
    fun ω hω => event_invariant q hq.hist R hq.res y _ hF k _ (piece_measurable k hs y) ω
      hω.1.2 (by simpa using hω.2)
  constructor
  · intro h
    have h3 := (key _ h).mpr h
    rwa [signFlip_involutive S mask ω] at h3
  · intro h
    exact (key ω h).mpr h

theorem indicator_decomp (k : ℕ) (P : Set (RandomSources S M)) (F : ι → RandomSources S M → ℝ) :
    P.indicator (fun ω => F (q.pivot k ω) ω) =
      fun ω => ∑ y, (P ∩ q.pivot k ⁻¹' {y}).indicator (F y) ω := by
  funext ω
  rw [Finset.sum_eq_single (q.pivot k ω)]
  · by_cases hω : ω ∈ P
    · rw [Set.indicator_of_mem hω,
        Set.indicator_of_mem (show ω ∈ P ∩ q.pivot k ⁻¹' {q.pivot k ω} from ⟨hω, rfl⟩)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω h.1)]
  · intro y _ hy
    exact Set.indicator_of_notMem (fun h => hy (by simpa using h.2.symm)) _
  · simp

theorem residual_indicator_eq (hq : LawHyp q v lam hgt) (k : ℕ) (s : Set (RandomSources S M))
    (f : ℝ → ℝ) :
    (s ∩ {ω | k < q.stop ω}).indicator (fun ω => f (q.residual k ω)) =
      (s ∩ {ω | k < q.stop ω}).indicator
        (fun ω => f (siteSuffix S lam (hgt (q.pivot k ω)) (v (q.pivot k ω)) ω)) := by
  funext ω
  by_cases hω : ω ∈ s ∩ {ω | k < q.stop ω}
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hq.res k ω hω.2]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]

theorem siteSuffix_abs_le (y : S) (h : ℕ) (ω : RandomSources S M) :
    |siteSuffix S lam h y ω| ≤ |lam| :=
  (siteSuffix_bound S lam h y ω).trans
    (div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num)))

theorem setIntegral_residual (hq : LawHyp q v lam hgt) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) :
    ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator (q.residual k) ω ∂sourcesLaw S M = 0 := by
  have h1 := residual_indicator_eq hq k s id
  simp only [id] at h1
  rw [show (fun ω => q.residual k ω) = q.residual k from rfl] at h1
  rw [h1, indicator_decomp k _ (fun y ω => siteSuffix S lam (hgt y) (v y) ω)]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun y _ => ?_
    have hE := q.history.le k _ (piece_measurable k hs y)
    exact integral_indicator_siteSuffix lam (hgt y) (v y) _ hE
      (piece_inv hq k hs y le_rfl)
  · intro y _
    exact integrable_indicator_bounded (siteSuffix_measurable S lam (hgt y) (v y)) |lam|
      (siteSuffix_abs_le (v y) (hgt y)) _ (q.history.le k _ (piece_measurable k hs y))

theorem setIntegral_residual_sq (hq : LawHyp q v lam hgt) (k : ℕ) {s : Set (RandomSources S M)}
    (hs : MeasurableSet[q.history k] s) :
    ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator (fun ω => q.residual k ω ^ 2) ω ∂sourcesLaw S M =
      ∫ ω, (s ∩ {ω | k < q.stop ω}).indicator
        (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) ω ∂sourcesLaw S M := by
  rw [residual_indicator_eq hq k s (fun x => x ^ 2),
    indicator_decomp k _ (fun y ω => siteSuffix S lam (hgt y) (v y) ω ^ 2),
    indicator_decomp k _ (fun y _ => lam ^ 2 / (3 * 4 ^ hgt y))]
  have hEm : ∀ y, MeasurableSet ((s ∩ {ω | k < q.stop ω}) ∩ q.pivot k ⁻¹' {y}) :=
    fun y => q.history.le k _ (piece_measurable k hs y)
  rw [integral_finset_sum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_indicator_siteSuffix_sq lam (hgt y) (v y) _ (hEm y)
      (fun n => piece_inv hq k hs y (by rintro _ rfl; exact ⟨n, rfl⟩)),
      integral_indicator_const _ (hEm y), smul_eq_mul, mul_comm]
  · intro y _
    exact (integrable_const _).indicator (hEm y)
  · intro y _
    refine integrable_indicator_bounded
      ((siteSuffix_measurable S lam (hgt y) (v y)).pow_const 2) (|lam| ^ 2) (fun ω => ?_) _ (hEm y)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (siteSuffix_abs_le (v y) (hgt y) ω) 2

theorem trunc_residual_eq (k : ℕ) :
    (truncTrial q).residual k = {ω | k < q.stop ω}.indicator (q.residual k) := by
  funext ω
  show (if k < q.stop ω then q.residual k ω else 0) = _
  by_cases h : k < q.stop ω
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω} from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | k < q.stop ω} from h)]

theorem residual_measurable (k : ℕ) : Measurable (q.residual k) :=
  ((q.residual_revealed k).mono (q.history.le (k + 1))).measurable

theorem integrable_trunc (hq : LawHyp q v lam hgt) (k : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |x| ≤ |lam| → |f x| ≤ C) :
    Integrable ({ω | k < q.stop ω}.indicator (fun ω => f (q.residual k ω))) (sourcesLaw S M) := by
  have hG : MeasurableSet {ω | k < q.stop ω} :=
    q.history.le k _ (stopping_lt_measurableSet q k)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (by simp))
  refine Integrable.of_bound ((hf.comp (residual_measurable k)).indicator hG).aestronglyMeasurable
    C (Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ {ω | k < q.stop ω}
  · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
    apply hC
    rw [hq.res k ω hω]
    exact siteSuffix_abs_le _ _ ω
  · rw [Set.indicator_of_notMem hω, norm_zero]; exact hC0

/-- The revealed residual is centered given the history. -/
theorem condExp_trunc_residual (hq : LawHyp q v lam hgt) (k : ℕ) :
    (sourcesLaw S M)[(truncTrial q).residual k | q.history k] =ᵐ[sourcesLaw S M] 0 := by
  rw [trunc_residual_eq]
  have hY := integrable_trunc hq k id measurable_id |lam| (fun x hx => hx)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (q.history.le k) hY
    (fun s _ _ => integrableOn_zero) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [integral_zero, ← integral_indicator (q.history.le k _ hs), Set.indicator_indicator]
  exact (setIntegral_residual hq k hs).symm

/-- The conditional second moment of the revealed residual given the history. -/
theorem condExp_trunc_residual_sq (hq : LawHyp q v lam hgt) (k : ℕ) :
    (sourcesLaw S M)[fun ω => (truncTrial q).residual k ω ^ 2 | q.history k] =ᵐ[sourcesLaw S M]
      {ω | k < q.stop ω}.indicator (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) := by
  have hsq : (fun ω => (truncTrial q).residual k ω ^ 2) =
      {ω | k < q.stop ω}.indicator (fun ω => q.residual k ω ^ 2) := by
    rw [trunc_residual_eq]
    funext ω
    by_cases hω : ω ∈ {ω | k < q.stop ω}
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω]; ring
  rw [hsq]
  have hY := integrable_trunc hq k (fun x => x ^ 2) (measurable_id.pow_const 2) (|lam| ^ 2)
    (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hGH := stopping_lt_measurableSet q k
  have hσ : StronglyMeasurable[q.history k] (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω))) :=
    ((measurable_of_countable (fun i : ι => lam ^ 2 / (3 * 4 ^ hgt i))).comp
      (q.pivot_predictable k)).stronglyMeasurable
  have hg : StronglyMeasurable[q.history k]
      ({ω | k < q.stop ω}.indicator (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω)))) :=
    hσ.indicator hGH
  have hgint : Integrable ({ω | k < q.stop ω}.indicator
      (fun ω => lam ^ 2 / (3 * 4 ^ hgt (q.pivot k ω)))) (sourcesLaw S M) := by
    refine Integrable.of_bound (hg.mono (q.history.le k)).aestronglyMeasurable (lam ^ 2)
      (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ {ω | k < q.stop ω}
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_self (sq_nonneg _) (by
        have : (1 : ℝ) ≤ 4 ^ hgt (q.pivot k ω) := one_le_pow₀ (by norm_num)
        linarith)
    · rw [Set.indicator_of_notMem hω, norm_zero]; positivity
  refine (ae_eq_condExp_of_forall_setIntegral_eq (q.history.le k) hY
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hg.aestronglyMeasurable).symm
  rw [← integral_indicator (q.history.le k _ hs), ← integral_indicator (q.history.le k _ hs),
    Set.indicator_indicator, Set.indicator_indicator]
  exact (setIntegral_residual_sq hq k hs).symm

theorem trunc_sq_eq (k : ℕ) :
    (fun ω => (truncTrial q).residual k ω ^ 2) =
      {ω | k < q.stop ω}.indicator (fun ω => q.residual k ω ^ 2) := by
  rw [trunc_residual_eq]
  funext ω
  by_cases hω : ω ∈ {ω | k < q.stop ω}
  · simp only [Set.indicator_of_mem hω]
  · simp only [Set.indicator_of_notMem hω]; ring

end TrialLaw

/-! ## The clearing trial -/

section Clearing

open AndersonAC.S78 AndersonAC.S2

theorem scaleCoupling_sq (n₀ : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    OAI.Anderson.scaleCoupling n₀ u ^ 2 = 3 * u / 4 ^ n₀ := by
  unfold OAI.Anderson.scaleCoupling
  have h2 : ((2 : ℝ) ^ n₀) ^ 2 = 4 ^ n₀ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow, Real.sq_sqrt (by positivity), h2]

/-- A pivot within `ℓ_j/2` of the core is coupled: it carries `j − n₀` exposed digits. -/
theorem near_coupled {d m n₀ : ℕ} {cP CP : ℝ} {qlag : ℝ → ℝ} {u : ℝ} {j : ℕ}
    {x : RunRecord d m} (hx : ClearingGoodAt cP CP qlag n₀ u j x) {B : Finset (ActiveSite x)}
    (hB : B.Nonempty) (hBmem : B.map (Function.Embedding.subtype _) ∈ x.components)
    (hsep : ∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
      ∀ y ∈ B.map (Function.Embedding.subtype _),
        separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) (hj : 1 ≤ j)
    {p : ActiveSite x} (hpB : p ∉ B)
    (hnear : distanceToCore (fun a b : ActiveSite x => physicalDistance d m a.val b.val) B p <
      inspectionRadius j / 2) :
    x.prefixLength p.val + n₀ = j := by
  obtain ⟨y, hyB, hy⟩ := exists_near_of_distanceToCore_lt hB hnear
  refine hx.coupled p.val p.property fun hpend => ?_
  have hnotB : p.val ∉ B.map (Function.Embedding.subtype _) := by
    rw [Finset.mem_map]
    rintro ⟨a, ha, hav⟩
    exact hpB (Subtype.val_injective hav ▸ ha)
  have hRl : inspectionRadius j < separationRadius j := by
    unfold inspectionRadius separationRadius
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  refine localized_pivot_excludes_old_marks (B.map (Function.Embedding.subtype _))
    (x.pending.filter (fun z => z ∉ B.map (Function.Embedding.subtype _))) _
    (separationRadius j) (inspectionRadius j) hRl
    ⟨y.val, Finset.mem_map_of_mem _ hyB, hy.le⟩ ?_ (Finset.mem_filter.mpr ⟨hpend, hnotB⟩)
  intro z hz y' hy'
  rw [Finset.mem_filter] at hz
  exact hsep z hz.1 hz.2 y' hy'

/-- **clearing trial bound residual sub-contract, proved.** -/
theorem clearingResidual_proof (d : ℕ) (cP CP : ℝ) (qlag : ℝ → ℝ)
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m)) :
    ClearingResidualStatement d (ClearingGood d cP CP qlag geo) := by
  refine ⟨4, 0, ?_⟩
  intro n₀ m _ hm u hu E j hj hsched M x hx B hB hBmem _ hsep order q hhist hresid
  have hxg := hx.1
  have hj1 : 1 ≤ j := by omega
  have hjm : j ≤ m := (Nat.div_le_self m 2).trans' hsched
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hq : LawHyp q Subtype.val (OAI.Anderson.scaleCoupling n₀ u) (fun i => x.prefixLength i.val) :=
    ⟨hhist, Subtype.val_injective, fun k ω hk => hresid k ω hk⟩
  have h4j : (0 : ℝ) < 4 ^ j := by positivity
  have h4m : (0 : ℝ) < 4 ^ m := by positivity
  have htu : u / 4 ^ j ≤ (stageScale u j m) := by
    unfold stageScale; have : 0 ≤ u / 4 ^ m := by positivity
    linarith
  have htpos : 0 < (stageScale u j m) := lt_of_lt_of_le (by positivity) htu
  -- coupled pivots: the variance and the size of the residual
  have hσ : ∀ i : ActiveSite x, x.prefixLength i.val + n₀ = j →
      (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength i.val) = u / 4 ^ j := by
    intro i hi
    rw [scaleCoupling_sq n₀ hu0.le, ← hi, pow_add]
    field_simp
  have hbound : ∀ i : ActiveSite x, x.prefixLength i.val + n₀ = j →
      |(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val ≤ 4 * Real.sqrt (stageScale u j m) := by
    intro i hi
    have hsq : (|(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val) ^ 2 = 3 * (u / 4 ^ j) := by
      have h2 : ((2 : ℝ) ^ x.prefixLength i.val) ^ 2 = 4 ^ x.prefixLength i.val := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, sq_abs, h2, ← hσ i hi]
      field_simp
    have h1 : |(OAI.Anderson.scaleCoupling n₀ u)| / 2 ^ x.prefixLength i.val ≤ Real.sqrt (4 * (stageScale u j m)) := by
      apply Real.le_sqrt_of_sq_le
      rw [hsq]; linarith
    have h2 : Real.sqrt (4 * (stageScale u j m)) = 2 * Real.sqrt (stageScale u j m) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h3 : 0 ≤ Real.sqrt (stageScale u j m) := Real.sqrt_nonneg (stageScale u j m)
    linarith
  have hcoupled : ∀ k ω, k < q.stop ω →
      distanceToCore (fun a b : ActiveSite x => physicalDistance d m a.val b.val) B
        (q.pivot k ω) < inspectionRadius j / 2 →
      x.prefixLength (q.pivot k ω).val + n₀ = j := by
    intro k ω hk hnear
    obtain ⟨_, hnotcore, -⟩ := q.heat k ω hk
    exact near_coupled hxg hB hBmem hsep hj1 hnotcore hnear
  refine
    { residual_bound := fun k ω hk hnear => ?_
      residual_integrable := fun k => ?_
      residual_square_integrable := fun k => ?_
      residual_mean := fun k => ?_
      residual_variance := fun k => ?_ }
  · have hk' : k < q.stop ω := hk
    show |(truncTrial q).residual k ω| ≤ 4 * Real.sqrt (stageScale u j m)
    rw [trunc_residual_eq, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω} from hk'),
      hq.res k ω hk']
    exact (siteSuffix_bound _ (OAI.Anderson.scaleCoupling n₀ u) _ _ ω).trans (hbound _ (hcoupled k ω hk' hnear))
  · rw [trunc_residual_eq]
    exact integrable_trunc hq k id measurable_id |(OAI.Anderson.scaleCoupling n₀ u)| (fun x hx => hx)
  · rw [trunc_sq_eq]
    exact integrable_trunc hq k (fun x => x ^ 2) (measurable_id.pow_const 2) (|(OAI.Anderson.scaleCoupling n₀ u)| ^ 2)
      (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  · filter_upwards [condExp_trunc_residual hq k] with ω hω _ _
    exact hω
  · refine ⟨fun ω => (stageScale u j m) - (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength (q.pivot k ω).val), ?_, ?_⟩
    · exact (stronglyMeasurable_const.sub
        ((measurable_of_countable (fun i : ActiveSite x =>
          (OAI.Anderson.scaleCoupling n₀ u) ^ 2 / (3 * 4 ^ x.prefixLength i.val))).comp
          (q.pivot_predictable k)).stronglyMeasurable)
    · filter_upwards [condExp_trunc_residual_sq hq k] with ω hω hk hnear
      have hk' : k < q.stop ω := hk
      have hc := hcoupled k ω hk' hnear
      rw [hσ _ hc]
      have hη : (stageScale u j m) - u / 4 ^ j = u / 4 ^ m := by unfold stageScale; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hη]; positivity
      · rw [hη, div_le_iff₀ htpos]
        have h2j : 2 * j ≤ m := by unfold clearingScheduled at hsched; omega
        have hpow : (4 : ℝ) ^ (2 * j) ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) h2j
        have hsq : (u / 4 ^ j) ^ 2 ≤ (stageScale u j m) * (stageScale u j m) := by
          have h0 : 0 ≤ u / 4 ^ j := by positivity
          nlinarith
        have : u / 4 ^ m ≤ 4 * (u / 4 ^ j) ^ 2 := by
          rw [div_pow, ← pow_mul, mul_comm j 2]
          rw [div_le_iff₀ h4m]
          have h4u : 1 ≤ 4 * u := by linarith [hu.1]
          have : 4 * (u ^ 2 / 4 ^ (2 * j)) * 4 ^ m ≥ 4 * (u ^ 2 / 4 ^ m) * 4 ^ m := by
            have : u ^ 2 / 4 ^ m ≤ u ^ 2 / 4 ^ (2 * j) :=
              div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) hpow
            nlinarith
          have h5 : 4 * (u ^ 2 / 4 ^ m) * 4 ^ m = 4 * u ^ 2 := by field_simp
          nlinarith
        nlinarith
      · show (sourcesLaw (S78.Torus d m) M)[fun ω => (truncTrial q).residual k ω ^ 2 | q.history k] ω = _
        rw [hω, Set.indicator_of_mem (show ω ∈ {ω | k < q.stop ω} from hk'), hσ _ hc]
        ring

end Clearing

end AndersonAC.AgentS78.Residual

namespace AndersonAC.AgentS78

/-- **clearing trial bound: the clearing first-trial bound (query-history variant)**, conditional only on the
uniform Proposition 6.6, the uniform drift contract, the blueprint concentration input and
the geometry sub-contract. Transport and residual law are proved. -/
theorem clearingTrialH_of_geometry {d : ℕ} (hd : 3 ≤ d)
    (hprep : PreparationUniformStatement) (hdrift : LeverageDriftUniformStatement)
    (hconc : AndersonAC.Blueprint.ConcentrationInput)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m))
    (hgeo : ClearingGeometryStatement d (ClearingGood d cP CP qlag geo) cP CP) :
    ClearingTrialStatementH d (ClearingGood d cP CP qlag geo) :=
  clearingTrialH_of_inputs' hd hprep hdrift hconc cP CP qlag hqlag geo hgeo
    (Residual.clearingResidual_proof d cP CP qlag geo)

end AndersonAC.AgentS78
