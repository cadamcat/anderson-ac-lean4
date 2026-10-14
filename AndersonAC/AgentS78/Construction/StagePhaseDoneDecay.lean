import AndersonAC.AgentS78.Construction.StagePhaseDoneRange
import AndersonAC.S6.CoreDecay

/-!
# The DONE exit of a clearing attempt: decay of the committed difference

agent-s78donea. Proof of the frozen sub-statement `DoneDecayStatement`
(07-assembly.tex:415–433). Instead of summing heat by heat (Lemma locality) and adding the core
(Corollary 6.3), the whole committed operation is treated as one elimination of
`O = A₀ \ A'` from the committed state `s₀ = x.endpoint`:

* along the block every scratch matrix is obtained from `(A₀, re M₀)` by Schur steps
  (`elimRel_reach`; a heat at an already removed site changes nothing on the active block);
* hence the scattering change `ds` of `survivorDifference s₀ s'` is a supported contraction for
  the cross block of `O` (`supported_change`);
* the cross block's projection weights decay in the collapsed distance to `O` for the terminals
  of `s₀` (`range_decay`, Lemma 6.2, using the hop structure of `s₀` from the record trace);
* Corollary 6.3 (`S6.core_decay`) and the terminal metric of `s₀` give the stated decay with
  `cA ≤ a/2`, `CA ≥ 4`, `PA ≥ 1`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78 AndersonAC.AgentS78Geo
open AndersonAC.S2 (Answer)
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {d m : ℕ}

/-! ## Elimination relation along the block -/

/-- `(A, Mn)` arises from `(A₀, M₀)` by Schur steps, up to entries off `A × A`; removed sites
of `A₀` have dead rows and columns. -/
structure ElimRel (A₀ : Finset (Torus d m)) (M₀ : Matrix (Torus d m) (Torus d m) ℝ)
    (A : Finset (Torus d m)) (Mn : Matrix (Torus d m) (Torus d m) ℝ) : Prop where
  sub : A ⊆ A₀
  seq : ∃ M'' : Matrix (Torus d m) (Torus d m) ℝ, CoreElim Finset.univ A₀ M₀ A M'' ∧
    ∀ i ∈ A, ∀ k ∈ A, M'' i k = Mn i k
  dead : ∀ q ∈ A₀, q ∉ A → ∀ i, i ≠ q → Mn i q = 0 ∧ Mn q i = 0

theorem elimRel_refl (A₀ : Finset (Torus d m)) (M₀ : Matrix (Torus d m) (Torus d m) ℝ) :
    ElimRel A₀ M₀ A₀ M₀ :=
  ⟨Finset.Subset.refl _, ⟨M₀, CoreElim.refl, fun _ _ _ _ => rfl⟩, fun q hq hq' => absurd hq hq'⟩

theorem elimRel_step {A₀ A : Finset (Torus d m)} {M₀ Mn : Matrix (Torus d m) (Torus d m) ℝ}
    (h : ElimRel A₀ M₀ A Mn) (p : Torus d m) (hp : p ∈ A₀) (ξ : ℝ) :
    ElimRel A₀ M₀ (A.erase p) (schurStepM Mn p ξ) := by
  obtain ⟨hsub, ⟨M'', hce, hag⟩, hdead⟩ := h
  refine ⟨(Finset.erase_subset _ _).trans hsub, ?_, ?_⟩
  · by_cases hpA : p ∈ A
    · refine ⟨schurStepM M'' p ξ, hce.step p ξ hpA (Finset.mem_univ p), fun i hi k hk => ?_⟩
      have hip : i ≠ p := (Finset.mem_erase.mp hi).1
      have hkp : k ≠ p := (Finset.mem_erase.mp hk).1
      have hiA := (Finset.mem_erase.mp hi).2
      have hkA := (Finset.mem_erase.mp hk).2
      unfold schurStepM
      rw [if_neg (by tauto), if_neg (by tauto)]
      rw [hag i hiA k hkA, hag i hiA p hpA, hag p hpA k hkA, hag p hpA p hpA]
    · rw [Finset.erase_eq_of_notMem hpA]
      refine ⟨M'', hce, fun i hi k hk => ?_⟩
      have hip : i ≠ p := fun h => hpA (h ▸ hi)
      have hkp : k ≠ p := fun h => hpA (h ▸ hk)
      unfold schurStepM
      rw [if_neg (by tauto), (hdead p hp hpA i hip).1, zero_mul, zero_div, sub_zero]
      exact hag i hi k hk
  · intro q hq hqA i hiq
    have hdq : q = p ∨ q ∉ A := by
      by_cases hqp : q = p
      · exact Or.inl hqp
      · exact Or.inr fun h => hqA (Finset.mem_erase.mpr ⟨hqp, h⟩)
    unfold schurStepM
    constructor
    · by_cases hc : i = p ∨ q = p
      · rw [if_pos hc, if_neg hiq]
      · rw [if_neg hc]
        have hqA' : q ∉ A := hdq.resolve_left (fun h => hc (Or.inr h))
        have hpq : p ≠ q := fun h => hc (Or.inr h.symm)
        rw [(hdead q hq hqA' i hiq).1, (hdead q hq hqA' p hpq).1, mul_zero, zero_div, sub_zero]
    · by_cases hc : q = p ∨ i = p
      · rw [if_pos hc, if_neg (Ne.symm hiq)]
      · rw [if_neg hc]
        have hqA' : q ∉ A := hdq.resolve_left (fun h => hc (Or.inl h))
        have hpq : p ≠ q := fun h => hc (Or.inl h.symm)
        rw [(hdead q hq hqA' i hiq).2, (hdead q hq hqA' p hpq).2, zero_mul, zero_div, sub_zero]

section Reach
variable (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

theorem elimRel_update (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) (hx : s.1 = x) (hI : ClrInv j u x s.2)
    (hE : ElimRel x.endpoint.active (fun a b => (x.endpoint.M a b).re) s.2.active s.2.Mnum) :
    ElimRel x.endpoint.active (fun a b => (x.endpoint.M a b).re)
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.active
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.Mnum := by
  subst hx
  unfold clearingUpdate
  dsimp only
  split
  · exact hE
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => exact hE
  | coreReady => exact hE
  | finish => exact hE
  | coreQuery p hcp =>
    have hmem := actionOf_coreQuery_mem j u s.1 s.2 p hcp hact
    obtain ⟨hpost, -⟩ := hI.post hcp
    have hpa : p ∈ s.2.active :=
      (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).2
    exact elimRel_step hE p (hI.sub hpa) _
  | heat p hg =>
    have hp0 : p ∈ s.1.endpoint.active := coupledActive_subset_active s.1 hg.1
    dsimp only
    split_ifs <;> exact elimRel_step hE p hp0 _

theorem elimRel_reach (x : RunRecord d m)
    (hD : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    ElimRel x.endpoint.active (fun a b => (x.endpoint.M a b).re) s.2.active s.2.Mnum := by
  induction h with
  | enter => exact elimRel_refl _ _
  | step s a hs _ ih =>
    exact elimRel_update n₀ j u x s a (clr_reach n₀ j u y x s hs).1
      (clrInv_reach n₀ j u y x hD s hs) ih

end Reach

theorem CoreElim.mono {core A A' : Finset (Torus d m)} {M M' : Matrix (Torus d m) (Torus d m) ℝ}
    (h : CoreElim core A M A' M') : ∀ core' : Finset (Torus d m), A \ A' ⊆ core' →
      CoreElim core' A M A' M' := by
  induction h with
  | refl => intro _ _; exact CoreElim.refl
  | @step A₁ M₁ p ξ hprev hp _ ih =>
    intro core' hc
    have hA₁ : A₁ ⊆ A := (CoreElim.sub hprev).1
    refine CoreElim.step p ξ (ih core' ?_) hp (hc (Finset.mem_sdiff.mpr ⟨hA₁ hp,
      Finset.notMem_erase p A₁⟩))
    intro z hz
    rw [Finset.mem_sdiff] at hz
    exact hc (Finset.mem_sdiff.mpr ⟨hz.1, fun h => hz.2 (Finset.mem_of_mem_erase h)⟩)

theorem fullInv_congr (A : Finset (Torus d m)) (M N : Matrix (Torus d m) (Torus d m) ℝ) (t : ℝ)
    (r : Torus d m → ℂ) (h : ∀ i ∈ A, ∀ k ∈ A, M i k = N i k) :
    fullInv A M t r = fullInv A N t r := by
  have : restrictM A M = restrictM A N := by
    ext a b; exact h a a.2 b b.2
  ext i k
  unfold fullInv
  rw [this]

/-! ## The decay -/

/-- **Proof of the decay sub-statement.** -/
theorem doneDecay_proof (d : ℕ) : DoneDecayStatement d := by
  intro cP CP hcP hCP Ctr _hCtr
  obtain ⟨ha, -⟩ := AndersonAC.SolS6.localization_rate_bound d cP hcP
  set a := AndersonAC.SolS6.localizationRate d cP with ha_def
  set L := 2 * Real.sqrt (CP / cP) with hL
  have hLpos : 0 < L := by
    have : 0 < CP / cP := div_pos (hcP.trans_le hCP) hcP
    positivity
  refine ⟨4, a / 2, 1, by norm_num, half_pos ha, zero_le_one, ?_⟩
  intro CA cA PA hCA hcA hcA' hPA
  refine ⟨0, min 1 ((cP / L ^ 2) ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro m n₀ j u E ρ C y x D _hN _hj hsch hu ht _hDs1 _hDs2 hbroad hrec hab s hs hne hf hdn
    _hphys _hmet _hhops
  intro s' s₀ t
  have ht0 : 0 < t := stageScale_pos' hu j m
  have ht1 : t ≤ 1 := (ht.trans_le (min_le_left _ _)).le
  have hs0 : s₀ = x.endpoint := D.last
  have hDx : IsDampedEndpoint x.endpoint x.r t := by
    have := D.I.physical (Fin.last D.k)
    rw [D.last, ← D.frozen] at this
    exact this
  have hmet0 : ∀ v w, physicalDistance d m v w / 2 - t ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) v w := by
    have := D.I.metric (Fin.last D.k)
    rw [D.last] at this
    exact this
  have hr : ∀ i, 0 < (x.r i).im := fun i => hcP.trans_le (hbroad i).1
  set A₀ := x.endpoint.active with hA₀
  set M₀ : Matrix (Torus d m) (Torus d m) ℝ := fun a b => (x.endpoint.M a b).re with hM₀
  have hsym : ∀ i k, M₀ i k = M₀ k i := fun i k => by
    simp only [hM₀]; rw [(hDx.1 i k).1]
  -- the elimination of `O = A₀ \ A'`
  have hI := clrInv_reach n₀ j u y x hDx s hs
  obtain ⟨hsub, ⟨M'', hce, hag⟩, -⟩ := elimRel_reach n₀ j u y x hDx s hs
  set A' := s.2.active with hA'
  set O := A₀ \ A' with hO
  have hce' : CoreElim O A₀ M₀ A' M'' := hce.mono O (Finset.Subset.refl _)
  have hdisj : Disjoint O A' := Finset.sdiff_disjoint
  obtain ⟨hnorm, hleft, hdsym⟩ :=
    supported_change t x.r O A₀ A' M₀ M'' ht0 hr hsym Finset.sdiff_subset hce' hdisj
  -- the hop structure of `s₀`
  obtain ⟨l₀, T₀, hT₀, hT₀term, -⟩ := hrec.trace
  obtain ⟨J, hJs, hJ1, hJadj, hJhops⟩ := hT₀.hops
  have hterm : Finset.univ \ A₀ = x.terminal := by
    rw [hA₀, hrec.activeCompl]; ext z; simp
  have hhop0 : ∀ a ∈ A₀, ∀ b ∈ A₀, M₀ a b ≠ J a b →
      terminalDistance (nnGraph d m) (Finset.univ \ A₀) a b = 0 := by
    intro a ha b hb hne
    rw [hterm, ← hT₀term]
    apply hJhops a ha b hb
    intro he
    apply hne
    simp only [hM₀, he, Complex.ofReal_re]
  have hrd := range_decay A₀ O M₀ hsym J hJs hJ1 hJadj hhop0 Finset.sdiff_subset t cP CP ht0 ht1
    hcP hCP x.r (fun i => ⟨(hbroad i).1, (Complex.im_le_norm _).trans (hbroad i).2⟩)
  -- Corollary 6.3
  set dg := chgDg t x.r A₀ M₀ A' M'' with hdg
  set p : Torus d m → ℝ := fun i => (x.r i).im with hp
  have hrel : chgDs t x.r A₀ M₀ A' M'' = (2 * Complex.I * (Real.sqrt t : ℂ)) •
      (AndersonAC.S6.sqrtDamping p * AndersonAC.S6.scaledInverse t dg *
        AndersonAC.S6.sqrtDamping p) := by
    ext i k
    simp only [chgDs, AndersonAC.S6.scaledInverse, AndersonAC.S6.sqrtDamping, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, ← hdg, ← hp]
    have hst : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0.le]
    rw [← hst]
    ring
  have hcd := AndersonAC.S6.core_decay t cP a L p (collRadius A₀ O)
    (xCross t x.r A₀ (restrictM A₀ M₀) O) (AndersonAC.S6.scaledInverse t dg)
    (chgDs t x.r A₀ M₀ A' M'') ht0 hcP hLpos.le (fun i => (hbroad i).1) hnorm hleft hdsym hrel
    (by simpa only [hL] using hrd)
  -- the survivor difference is the scaled change
  obtain ⟨hAeq, -⟩ := clr_done_active j u x s.2 hI hab hsch hne hf hdn
  have hsd : survivorDifference s₀ s' t = AndersonAC.S6.scaledInverse t dg := by
    rw [hs0]
    show survivorDifference x.endpoint (clearingDoneExit x s.2).endpoint t = _
    ext i k
    have hg' : (clearingDoneExit x s.2).endpoint.g i k =
        if i ∈ A' ∧ k ∈ A' then s.2.hatG i k else 0 := by
      rw [clr_doneExit_endpoint x s.2 hAeq]
    have ha' : (clearingDoneExit x s.2).endpoint.active = A' := by
      rw [clr_doneExit_endpoint x s.2 hAeq]
    simp only [survivorDifference, normalizedInverse, AndersonAC.S6.scaledInverse,
      Matrix.smul_apply, smul_eq_mul, hdg, chgDg, ha', hg']
    by_cases hik : i ∈ A' ∧ k ∈ A'
    · simp only [if_pos hik]
      rw [hI.inv i k hik.1 hik.2, ← fullInv_congr _ M'' s.2.Mnum t x.r hag,
        damped_g_eq_activeInverse x t hDx i (hsub hik.1) k (hsub hik.2)]
      ring
    · simp only [if_neg hik, mul_zero]
  have hO' : s₀.active \ s'.active = O := by
    rw [hs0]
    show x.endpoint.active \ (clearingDoneExit x s.2).endpoint.active = _
    rw [clr_doneExit_endpoint x s.2 hAeq]
  intro i k
  rw [hsd, hO']
  refine (hcd i k).trans ?_
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have htL : t ≤ (cP / L ^ 2) ^ 2 := (ht.trans_le (min_le_right _ _)).le
  have hsqrt_le : Real.sqrt t ≤ cP / L ^ 2 := by
    calc Real.sqrt t ≤ Real.sqrt ((cP / L ^ 2) ^ 2) := Real.sqrt_le_sqrt htL
      _ = cP / L ^ 2 := Real.sqrt_sq (by positivity)
  have hL2 : 0 < L ^ 2 := by positivity
  have hpref : L ^ 2 / (cP * Real.sqrt t) ≤ t ^ (-PA) := by
    have h1 : L ^ 2 * Real.sqrt t ≤ cP := by
      rw [le_div_iff₀ hL2] at hsqrt_le; linarith
    have h2 : L ^ 2 / (cP * Real.sqrt t) ≤ t⁻¹ := by
      have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
      have e1 : L ^ 2 / (cP * Real.sqrt t) =
          (L ^ 2 * Real.sqrt t / cP) * (Real.sqrt t * Real.sqrt t)⁻¹ := by
        first
          | (field_simp; done)
          | (field_simp; ring)
      rw [hss] at e1
      calc L ^ 2 / (cP * Real.sqrt t) = (L ^ 2 * Real.sqrt t / cP) * t⁻¹ := e1
        _ ≤ 1 * t⁻¹ := mul_le_mul_of_nonneg_right ((div_le_one hcP).mpr h1)
            (inv_nonneg.mpr ht0.le)
        _ = t⁻¹ := one_mul _
    refine h2.trans ?_
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
  set τ' := t ^ (-1.03 : ℝ) with hτ'
  have hτ1 : 1 ≤ τ' := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
  have hX : ∀ i, max (distanceTo (physicalDistance d m) O i - CA * τ') 0 ≤
      2 * collRadius A₀ O i := by
    intro i
    have hcr0 : 0 ≤ collRadius A₀ O i := le_max_right _ _
    apply max_le _ (by linarith)
    by_cases hOe : O.Nonempty
    · obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' hOe
        (terminalDistance (nnGraph d m) (Finset.univ \ A₀) i)
      have hdist : distanceTo (physicalDistance d m) O i ≤ physicalDistance d m i b := by
        apply csInf_le
        · refine ⟨0, ?_⟩
          rintro z ⟨y, -, rfl⟩
          unfold physicalDistance; positivity
        · exact ⟨b, hb, rfl⟩
      have hcr : terminalDistance (nnGraph d m) (Finset.univ \ A₀) i b - 1 ≤ collRadius A₀ O i := by
        unfold collRadius AndersonAC.S6.distanceToCore
        rw [dif_pos hOe, hbeq]
        exact le_max_left _ _
      have hm := hmet0 i b
      nlinarith
    · have h0 : distanceTo (physicalDistance d m) O i = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hOe]
        simp [distanceTo]
      rw [h0]
      nlinarith
  have hcA0 : 0 ≤ cA := hcA.le
  apply mul_le_mul hpref _ (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
  apply Real.exp_le_exp.mpr
  have hXi := hX i
  have hXk := hX k
  have hX0i : 0 ≤ max (distanceTo (physicalDistance d m) O i - CA * τ') 0 := le_max_right _ _
  have hX0k : 0 ≤ max (distanceTo (physicalDistance d m) O k - CA * τ') 0 := le_max_right _ _
  have h1 : cA * (max (distanceTo (physicalDistance d m) O i - CA * τ') 0 +
      max (distanceTo (physicalDistance d m) O k - CA * τ') 0) ≤
      a * (collRadius A₀ O i + collRadius A₀ O k) := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 ht0.le]

end AndersonAC.AgentS78.DoneA
