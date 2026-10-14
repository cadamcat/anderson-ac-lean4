import AndersonAC.AgentS78.Construction.StagePhaseDoneSnap
import AndersonAC.AgentS78.Construction.StagePhaseDoneCT
import AndersonAC.AgentS78.Construction.StagePhaseTrace
import AndersonAC.S78.Statements

/-!
# The DONE exit of a clearing attempt: heat part, core part, assembly. 07-assembly.tex:399–433. On the final survivors `A'` of a DONE exit the
committed difference splits at the core-phase snapshot `sh` (StagePhaseDoneSnap.lean):

  `survivorDifference x.endpoint s' t = heatPart + corePart`,

* `heatPart = √t (sh.hatG − g0)` on `A'`: bounded by the S6 heat budgets, which hold at the
  snapshot (`heat_bounds`: entry `√t t^{.42δ}`, squared row `t^{.25δ}`, Frobenius
  `n_h t^{−.01δ} ≤ t^{−1−.47δ}`);
* `corePart = √t (fullInv A' M' − fullInv A Mh)` on `A'`: the core completion (Lemma 6.1,
  `DoneCoreStatement`, sub-statement);
* both combine by `S78.successful_clearing_distortions`.

The decay clause is the sub-statement `DoneDecayStatement` (Lemma locality for the heats,
Corollary 6.3 for the core, 07-assembly.tex:415–433). The Combes–Thomas clause is
`endpoint_ct_phys` (StagePhaseDoneCT.lean).

`clearingDoneAnalytic_of_parts : DoneCoreStatement d → DoneDecayStatement d →
ClearingDoneAnalyticStatement d`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78
open AndersonAC.S2 (Answer)

variable {d m : ℕ}

/-! ## The heat part -/

/-- The difference `√t (hg − g0)` restricted to `A`. -/
def restrictedDiff (t : ℝ) (A : Finset (Torus d m)) (hg g0 : Matrix (Torus d m) (Torus d m) ℂ) :
    Matrix (Torus d m) (Torus d m) ℂ := fun i k =>
  if i ∈ A ∧ k ∈ A then (Real.sqrt t : ℂ) * (hg i k - g0 i k) else 0

theorem restrictedDiff_norm_le (t : ℝ) (A : Finset (Torus d m))
    (hg g0 : Matrix (Torus d m) (Torus d m) ℂ) (i k : Torus d m) :
    ‖restrictedDiff t A hg g0 i k‖ ≤ ‖AndersonAC.S6.scaledInverse t (hg - g0) i k‖ := by
  unfold restrictedDiff AndersonAC.S6.scaledInverse
  split_ifs
  · simp
  · simp only [norm_zero]; positivity

/-- **The heat part from the S6 budgets.** -/
theorem heat_bounds (t : ℝ) (ht : 0 < t) (A : Finset (Torus d m))
    (g0 hg : Matrix (Torus d m) (Torus d m) ℂ) (hB : AndersonAC.S6.BudgetsHold t g0 hg) :
    (∀ i k, ‖restrictedDiff t A hg g0 i k‖ ≤ Real.sqrt t * t ^ (0.42 * delta)) ∧
    (∀ i, rowTwo (restrictedDiff t A hg g0) i ≤ t ^ (0.25 * delta)) ∧
    frobeniusSq (restrictedDiff t A hg g0) ≤ t ^ (-1 - 0.47 * delta) := by
  obtain ⟨hE, hR, hF⟩ := hB
  have hrow : ∀ i, rowTwo (restrictedDiff t A hg g0) i ≤
      AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t (hg - g0)) i := by
    intro i
    unfold rowTwo AndersonAC.S6.sqRow
    exact Finset.sum_le_sum fun k _ =>
      pow_le_pow_left₀ (norm_nonneg _) (restrictedDiff_norm_le t A hg g0 i k) 2
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    refine (restrictedDiff_norm_le t A hg g0 i k).trans ?_
    unfold AndersonAC.S6.scaledInverse
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := hE i k
    have heq : AndersonAC.S6.entryBudget t = t ^ (0.42 * delta) := by
      unfold AndersonAC.S6.entryBudget; norm_num [AndersonAC.S6.delta, delta]
    rw [heq] at h1
    exact mul_le_mul_of_nonneg_left (by simpa [Matrix.sub_apply] using h1) (Real.sqrt_nonneg _)
  · intro i
    refine (hrow i).trans ((hR i).trans_eq ?_)
    unfold AndersonAC.S6.rowBudget; norm_num [AndersonAC.S6.delta, delta]
  · have h1 : frobeniusSq (restrictedDiff t A hg g0) ≤
        AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t (hg - g0)) :=
      Finset.sum_le_sum fun i _ => hrow i
    refine h1.trans (hF.trans ?_)
    unfold AndersonAC.S6.frobeniusBudget AndersonAC.S6.heatLimit
    have hfl : ((⌊t ^ (-1 - AndersonAC.S6.eh)⌋₊ : ℕ) : ℝ) ≤ t ^ (-1 - AndersonAC.S6.eh) :=
      Nat.floor_le (Real.rpow_nonneg ht.le _)
    calc ((⌊t ^ (-1 - AndersonAC.S6.eh)⌋₊ : ℕ) : ℝ) * t ^ (-(1 / 100) * AndersonAC.S6.delta)
        ≤ t ^ (-1 - AndersonAC.S6.eh) * t ^ (-(1 / 100) * AndersonAC.S6.delta) :=
          mul_le_mul_of_nonneg_right hfl (Real.rpow_nonneg ht.le _)
      _ = t ^ (-1 - 0.47 * delta) := by
          rw [← Real.rpow_add ht]
          congr 1
          norm_num [AndersonAC.S6.eh, AndersonAC.S6.delta, delta]

/-! ## The core part: sub-statement -/

/-- The core-completion difference on the final survivors `A'`. -/
def coreDiff (t : ℝ) (r : Torus d m → ℂ) (A : Finset (Torus d m))
    (Mh : Matrix (Torus d m) (Torus d m) ℝ) (A' : Finset (Torus d m))
    (M' : Matrix (Torus d m) (Torus d m) ℝ) : Matrix (Torus d m) (Torus d m) ℂ := fun i k =>
  if i ∈ A' ∧ k ∈ A' then (Real.sqrt t : ℂ) * (fullInv A' M' t r i k - fullInv A Mh t r i k)
  else 0

/-- **Core completion on the torus scratch data** (sub-statement; Lemma 6.1,
06-clearing.tex:82–182, applied at the core-phase snapshot, 07-assembly.tex:399–413).
From a snapshot `(A, Mh)` with the projection cap `xReady`, eliminating the whole core
sequentially (`CoreElim`, arbitrary real core values) changes the scaled inverse on the
survivors by at most the Lemma 6.1 bounds (`l = t^{1+e0}`, `|B| ≤ t^{−ν}`). -/
def DoneCoreStatement (d : ℕ) : Prop :=
  ∀ cP CP : ℝ, 0 < cP → cP ≤ CP →
  ∃ Cc t₀ : ℝ, 1 ≤ Cc ∧ 0 < t₀ ∧
  ∀ {m : ℕ} (t : ℝ) (r : Torus d m → ℂ) (core A A' : Finset (Torus d m))
    (Mh M' : Matrix (Torus d m) (Torus d m) ℝ),
    0 < t → t < t₀ → (∀ i, cP ≤ (r i).im ∧ ‖r i‖ ≤ CP) →
    (∀ i k, Mh i k = Mh k i) → core.Nonempty → core ⊆ A → (core.card : ℝ) ≤ t ^ (-nu d) →
    xReady t r A (restrictM A Mh) core →
    CoreElim core A Mh A' M' → Disjoint core A' →
    (∀ i k, ‖coreDiff t r A Mh A' M' i k‖ ≤ Cc * Real.sqrt t * t ^ (0.44 * delta)) ∧
    (∀ i, rowTwo (coreDiff t r A Mh A' M') i ≤ Cc * t ^ (0.44 * delta)) ∧
    frobeniusSq (coreDiff t r A Mh A' M') ≤ Cc * t ^ (-1 - nu d)

/-- **The decay clause** of `ClearingDoneAnalyticStatement` (sub-statement, same
hypotheses; 07-assembly.tex:415–433: Lemma locality for each heat, Corollary 6.3 for the core,
the terminal metric). -/
def DoneDecayStatement (d : ℕ) : Prop :=
  ∀ cP CP : ℝ, 0 < cP → cP ≤ CP → ∀ Ctr : ℝ, 2 ≤ Ctr →
  ∃ CA₀ cA₀ PA₀ : ℝ, 1 ≤ CA₀ ∧ 0 < cA₀ ∧ 0 ≤ PA₀ ∧
  ∀ CA cA PA : ℝ, CA₀ ≤ CA → 0 < cA → cA ≤ cA₀ → PA₀ ≤ PA →
  ∃ N : ℕ, ∃ t₀ : ℝ, 0 < t₀ ∧
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (y : Torus d m) (x : RunRecord d m)
    (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
    N ≤ n₀ → n₀ < j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    stageScale u j m < t₀ →
    2 * clearRadius d m j u ≤ D.I.Ds → D.I.Ds ≤ Ctr * clearRadius d m j u →
    (∀ i, cP ≤ (x.r i).im ∧ ‖x.r i‖ ≤ CP) →
    ClearRec Ctr n₀ u j x D.I.anchor → x.aborted = false →
    ∀ s : RunRecord d m × ClearScratch d m,
      BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      IsDampedEndpoint (clearingDoneExit x s.2).endpoint x.r (stageScale u j m) →
      (∀ v w, physicalDistance d m v w / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (Finset.univ \ (clearingDoneExit x s.2).endpoint.active) v w) →
      (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
        (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
        ∀ a ∈ (clearingDoneExit x s.2).endpoint.active, ∀ b ∈ (clearingDoneExit x s.2).endpoint.active,
          (clearingDoneExit x s.2).endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
          terminalDistance (nnGraph d m) (Finset.univ \ (clearingDoneExit x s.2).endpoint.active) a b = 0) →
      let s' := (clearingDoneExit x s.2).endpoint
      let s₀ := D.I.state (Fin.last D.k)
      let t := stageScale u j m
      (∀ i k, ‖survivorDifference s₀ s' t i k‖ ≤ t ^ (-PA) * Real.exp (-cA * t *
        (max (distanceTo (physicalDistance d m) (s₀.active \ s'.active) i - CA * t ^ (-1.03 : ℝ)) 0 +
         max (distanceTo (physicalDistance d m) (s₀.active \ s'.active) k - CA * t ^ (-1.03 : ℝ)) 0)))

/-! ## The split at the snapshot -/

/-- **The DONE difference splits at the core-phase snapshot** into the heat part and the core
part. -/
theorem done_split (n₀ j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (hDx : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : s.2.core ≠ ∅)
    (hf : s.2.failed = false) (hdn : s.2.done = true) :
    ∃ sh : ClearScratch d m, Snap (stageScale u j m) x.r x.endpoint.g sh ∧ sh.core = s.2.core ∧
      CoreElim s.2.core sh.active sh.Mnum s.2.active s.2.Mnum ∧ Disjoint s.2.core s.2.active ∧
      survivorDifference x.endpoint (clearingDoneExit x s.2).endpoint (stageScale u j m) =
        restrictedDiff (stageScale u j m) s.2.active sh.hatG x.endpoint.g +
          coreDiff (stageScale u j m) x.r sh.active sh.Mnum s.2.active s.2.Mnum := by
  have hI := clrInv_reach n₀ j u y x hDx s hs
  obtain ⟨hcp, hl⟩ := hI.done hdn hf hab hsch hne
  obtain ⟨sh, hsh, hcore, -, hce⟩ := (snapInv_reach n₀ j u y x hDx s hs).snap hf hcp
  have hdisj : Disjoint s.2.core s.2.active := by
    rw [Finset.disjoint_iff_inter_eq_empty, (hI.post hcp).1, hl]
  obtain ⟨hA, -⟩ := clr_done_active j u x s.2 hI hab hsch hne hf hdn
  refine ⟨sh, hsh, hcore, hce, hdisj, ?_⟩
  ext i k
  have hg' : (clearingDoneExit x s.2).endpoint.g i k =
      if i ∈ s.2.active ∧ k ∈ s.2.active then s.2.hatG i k else 0 := by
    rw [clr_doneExit_endpoint x s.2 hA]
  have ha' : (clearingDoneExit x s.2).endpoint.active = s.2.active := by
    rw [clr_doneExit_endpoint x s.2 hA]
  simp only [survivorDifference, normalizedInverse, Matrix.smul_apply, smul_eq_mul,
    restrictedDiff, coreDiff, Matrix.add_apply, ha', hg']
  by_cases hik : i ∈ s.2.active ∧ k ∈ s.2.active
  · simp only [if_pos hik]
    have h1 := hI.inv i k hik.1 hik.2
    have h2 := hsh.inv i k (hce.sub.1 hik.1) (hce.sub.1 hik.2)
    rw [← h1, ← h2]
    ring
  · simp only [if_neg hik, add_zero]

/-! ## Assembly -/

/-- **`ClearingDoneAnalyticStatement` from its two sub-statement** (core completion on
the scratch data and the decay clause); the Combes–Thomas clause and the heat part are proved
here. -/
theorem clearingDoneAnalytic_of_parts (hd : 3 ≤ d) (hcore : DoneCoreStatement d)
    (hdecay : DoneDecayStatement d) : ClearingDoneAnalyticStatement d := by
  intro cP CP hcP hCP Ctr hCtr
  obtain ⟨Cc, tc, hCc, htc, hcoreM⟩ := hcore cP CP hcP hCP
  obtain ⟨C', ts, hC'pos, hts, hdist⟩ := successful_clearing_distortions d hd Cc hCc
  obtain ⟨CD, cD, PD, hCD, hcD, hPD, hdec⟩ := hdecay cP CP hcP hCP Ctr hCtr
  have ha := (AndersonAC.SolS6.localization_rate_bound d cP hcP).1
  refine ⟨max (max CD C') (4 / (3 * cP)), min cD (AndersonAC.SolS6.localizationRate d cP), PD,
    le_max_of_le_left (le_max_of_le_left hCD), lt_min hcD ha, hPD, ?_⟩
  intro CA cA PA hCA hcA hcA' hPA
  have hCAD : CD ≤ CA := (le_max_left _ _).trans ((le_max_left _ _).trans hCA)
  have hCAC : C' ≤ CA := (le_max_right _ _).trans ((le_max_left _ _).trans hCA)
  have hCAT : 4 / (3 * cP) ≤ CA := (le_max_right _ _).trans hCA
  obtain ⟨N, td, htd, hdecM⟩ := hdec CA cA PA hCAD hcA (hcA'.trans (min_le_left _ _)) hPA
  refine ⟨N, min (min td tc) (min ts 1), lt_min (lt_min htd htc) (lt_min hts one_pos), ?_⟩
  intro m n₀ j u E ρ C y x D hN hj hsch hu ht hDs1 hDs2 hbroad hrec hab s hs hne hf hdn hphys
    hmet hhops
  have hdecay' := hdecM n₀ j u E ρ C y x D hN hj hsch hu
    (ht.trans_le ((min_le_left _ _).trans (min_le_left _ _))) hDs1 hDs2 hbroad hrec hab s hs
    hne hf hdn hphys hmet hhops
  intro s' s₀ t
  have ht0 : 0 < t := stageScale_pos' hu j m
  have htc' : t < tc := ht.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hts' : t < min ts 1 := ht.trans_le (min_le_right _ _)
  have ht1 : t ≤ 1 := (hts'.trans_le (min_le_right _ _)).le
  have hs0 : s₀ = x.endpoint := D.last
  have hDx : IsDampedEndpoint x.endpoint x.r t := by
    have := D.I.physical (Fin.last D.k)
    rw [D.last, ← D.frozen] at this
    exact this
  -- Combes–Thomas
  obtain ⟨J, hJs, hJ1, hJadj, hhop⟩ := hhops
  have hCT := endpoint_ct_phys s' x.r t cP CA cA ht0 ht1 hcP (fun i => (hbroad i).1) hCAT hcA
    (hcA'.trans (min_le_right _ _)) hphys hmet J hJs hJ1 hJadj hhop
  -- the split, the heat part and the core part
  obtain ⟨sh, hsh, hcore', hce, hdisj, hsplit⟩ :=
    done_split n₀ j u y x hDx s hs hab hsch hne hf hdn
  obtain ⟨B, hb⟩ := done_basic n₀ j u y x hDx s hs hab hsch hne hf hdn
  have hcard : (s.2.core.card : ℝ) ≤ t ^ (-nu d) := by
    rw [hb.core]; exact hb.elig.2.2.1
  obtain ⟨hhE, hhR, hhF⟩ := heat_bounds t ht0 s.2.active x.endpoint.g sh.hatG hsh.budgets
  obtain ⟨hcE, hcR, hcF⟩ := hcoreM t x.r s.2.core sh.active s.2.active sh.Mnum s.2.Mnum ht0 htc'
    hbroad hsh.symm (Finset.nonempty_iff_ne_empty.mpr hne) (hcore' ▸ hsh.coreSub) hcard
    (hcore' ▸ hsh.ready) hce hdisj
  obtain ⟨hE, hR, hF⟩ := hdist (Torus d m) _ _ t ht0 hts' hhE hhR hhF hcE hcR hcF
  have hsd : survivorDifference s₀ s' t =
      restrictedDiff t s.2.active sh.hatG x.endpoint.g +
        coreDiff t x.r sh.active sh.Mnum s.2.active s.2.Mnum := by
    rw [hs0]; exact hsplit
  have hsqrt : 0 ≤ Real.sqrt t * t ^ (0.42 * delta) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg ht0.le _)
  refine ⟨hCT, ?_, ?_, ?_, hdecay'⟩
  · intro i k
    rw [hsd]
    refine (hE i k).trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hCAC hsqrt
  · intro i
    rw [hsd]
    exact (hR i).trans (mul_le_mul_of_nonneg_right hCAC (Real.rpow_nonneg ht0.le _))
  · rw [hsd]
    exact hF.trans (mul_le_mul_of_nonneg_right hCAC (Real.rpow_nonneg ht0.le _))

end AndersonAC.AgentS78.DoneA
