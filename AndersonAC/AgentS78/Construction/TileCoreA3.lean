import AndersonAC.AgentS78.Construction.TileTransfer
import AndersonAC.AgentS78.PadNorm
import AndersonAC.S45.MatrixProbProof

/-!
# WP10 construction, C4a core, piece A3: a failed first trial crosses a monitored budget

agent-s78trial (2026-10-14). A3a: along the slot recursion the partial sums of the stopped
monitored records (`tileRaw`) are the padded trial records since the trial start
(`partialSum_tileRaw`), and their norms dominate the four quantities of `S45.localBudget`
(`monitorOf_norm_*`). Hence a failure whose candidate violates a local budget is a crossing.
A3b (`TileTransferStatement`, TileTransfer.lean) excludes every other failure (05:844–860).
`tileFailCrossing_of_transfer : TileTransferStatement d C → TileFailCrossingStatement d C`.
-/

open MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-! ## Norm facts (L2 operator norm) -/

theorem entry_le_l2 {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ 𝕜) (i : ι) (k : κ) : ‖A i k‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single k (1 : 𝕜))
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι 𝕜).symm (A *ᵥ (EuclideanSpace.single k (1 : 𝕜)))) i
  convert this using 2
  simp

theorem real_le_complex {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    ‖A‖ ≤ ‖A.map (fun a => (a : ℂ))‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := Matrix.l2_opNorm_mulVec (A.map (fun a => (a : ℂ)))
    ((EuclideanSpace.equiv ι ℂ).symm (fun i => ((x i : ℝ) : ℂ)))
  have e1 : ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => ((x i : ℝ) : ℂ))‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]; simp
  rw [e1] at h
  refine le_trans (le_of_eq ?_) h
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  have hc : ((A.map fun a => (a : ℂ)) *ᵥ fun i => ((x.ofLp i : ℝ) : ℂ)) i =
      (((A *ᵥ x.ofLp) i : ℝ) : ℂ) := by
    simp [Matrix.mulVec, dotProduct]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem submatrix_norm_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (f : κ → ι) (hf : Function.Injective f) (N : Matrix ι ι ℂ) :
    ‖N.submatrix f f‖ ≤ ‖N‖ := by
  have hP := norm_inclMat_le f hf
  have hPH : ‖(inclMat f)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hP
  rw [← inclMat_block f N]
  calc ‖(inclMat f)ᴴ * N * inclMat f‖ ≤ ‖(inclMat f)ᴴ * N‖ * ‖inclMat f‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(inclMat f)ᴴ‖ * ‖N‖) * 1 := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖N‖) * 1 := by gcongr
    _ = ‖N‖ := by ring

theorem padInto_submatrix {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D)
    (he : Function.Injective e) (A : S45.CMat α) : (padInto D e A).submatrix e e = A := by
  ext a b
  simp only [submatrix_apply, padInto]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy; simp [he.eq_iff, hy]
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [he.eq_iff, hy]
  · simp

theorem padInto_norm_ge {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D)
    (he : Function.Injective e) (A : S45.CMat α) : ‖A‖ ≤ ‖padInto D e A‖ := by
  have := submatrix_norm_le e he (padInto D e A)
  rwa [padInto_submatrix D e he] at this

theorem mask_norm_le {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (J : S45.CMat ι) :
    ‖S45.mask S J‖ ≤ ‖S45.restrict J S‖ := by
  have hsub : (S45.mask S J).submatrix (fun i : S => i.val) (fun i : S => i.val) =
      S45.restrict J S := by
    ext a b; simp [S45.mask, S45.pad, S45.restrict, a.2, b.2]
  have := norm_submatrix_of_support (fun i : S => i.val) Subtype.val_injective (S45.mask S J)
    (by
      intro i j h
      simp only [S45.mask, S45.pad]
      rcases h with h | h
      · have : i ∉ S := fun hi => h ⟨i, hi⟩ rfl
        simp [this]
      · have : j ∉ S := fun hj => h ⟨j, hj⟩ rfl
        simp [this])
  rw [hsub] at this
  exact this.ge

theorem dilation_norm {P H : Type*} [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
    (B : Matrix P H ℂ) : ‖S45.dilation B‖ = ‖B‖ :=
  (AndersonAC.AgentS45.dilation_square_proof B).2.2

theorem scalarDilation_norm_ge (u : ℂ) : ‖u‖ ≤ ‖scalarDilation u‖ := by
  have := entry_le_l2 (scalarDilation u) 0 1
  simpa [scalarDilation] using this

theorem scalarBlock_norm_ge (a : ℝ) : |a| ≤ ‖scalarBlock a‖ := by
  have := entry_le_l2 (scalarBlock a) 0 0
  simpa [scalarBlock, Complex.norm_real, Real.norm_eq_abs] using this

/-! ## The monitor map -/

section Mon
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem embS_injective : Function.Injective (embS P j T) := by
  intro a b h; simp only [embS, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem embJ_injective : Function.Injective (embJ P j T) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [embJ, Fin.mk.injEq] at h
  · exact congrArg Sum.inl ((innerPorts P j T).equivFin.injective (Fin.ext h))
  · have := ((innerPorts P j T).equivFin a).isLt; omega
  · have := ((innerPorts P j T).equivFin b).isLt; omega
  · exact congrArg Sum.inr ((innerPorts P j T).equivFin.injective (Fin.ext (by omega)))

theorem embL_injective : Function.Injective (embL P j T) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [embL, Fin.mk.injEq] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := a.isLt; omega
  · have := b.isLt; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

/-- The monitored value of a record tuple (the branches of `tileEval`). -/
def monitorOf (i : Fin (monitorCount P j T)) (u : Port d m → ℂ) (Ra Rr : Port d m → ℝ)
    (J : S45.CMat (Port d m)) (L : S45.RMat (Port d m)) :
    S45.CMat (Fin (monitorDim P j T)) :=
  if h1 : i.val < (innerPorts P j T).card then
    padInto _ (embS P j T) (scalarDilation (u ((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩)))
  else if h2 : i.val < 2 * (innerPorts P j T).card then
    padInto _ (embS P j T) (scalarBlock (Ra ((innerPorts P j T).equivFin.symm
      ⟨i.val - (innerPorts P j T).card, by omega⟩)))
  else if h3 : i.val < 3 * (innerPorts P j T).card then
    padInto _ (embS P j T) (scalarBlock (Rr ((innerPorts P j T).equivFin.symm
      ⟨i.val - 2 * (innerPorts P j T).card, by omega⟩)))
  else if i.val = 3 * (innerPorts P j T).card then
    padInto _ (embJ P j T) (S45.dilation (S45.restrict J (innerPorts P j T)))
  else
    padInto _ (embL P j T) (S45.dilation ((S45.pullback ((P.cover j).cover.coords T).B L).map
      (fun a => (a : ℂ))))

theorem padInto_add {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D)
    (A B : S45.CMat α) : padInto D e (A + B) = padInto D e A + padInto D e B := by
  ext a b
  simp only [padInto, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem padInto_zero {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D) :
    padInto D e (0 : S45.CMat α) = 0 := by
  ext a b; simp [padInto]

theorem dilation_add {P H : Type*} (A B : Matrix P H ℂ) :
    S45.dilation (A + B) = S45.dilation A + S45.dilation B := by
  simp [S45.dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]

theorem dilation_zero {P H : Type*} : S45.dilation (0 : Matrix P H ℂ) = 0 := by
  simp [S45.dilation]

theorem monitorOf_add (i : Fin (monitorCount P j T)) (u u' : Port d m → ℂ)
    (Ra Ra' Rr Rr' : Port d m → ℝ) (J J' : S45.CMat (Port d m)) (L L' : S45.RMat (Port d m)) :
    monitorOf P j T i (u + u') (Ra + Ra') (Rr + Rr') (J + J') (L + L') =
      monitorOf P j T i u Ra Rr J L + monitorOf P j T i u' Ra' Rr' J' L' := by
  unfold monitorOf
  split_ifs
  · rw [← padInto_add]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarDilation]
  · rw [← padInto_add]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarBlock]
  · rw [← padInto_add]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarBlock]
  · rw [← padInto_add, ← dilation_add]; congr 2
  · rw [← padInto_add, ← dilation_add]; congr 2
    ext a b; simp [S45.pullback, Matrix.mul_add, Matrix.add_mul]

theorem monitorOf_zero (i : Fin (monitorCount P j T)) :
    monitorOf P j T i 0 0 0 0 0 = 0 := by
  unfold monitorOf
  split_ifs
  · rw [← padInto_zero (monitorDim P j T) (embS P j T)]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarDilation]
  · rw [← padInto_zero (monitorDim P j T) (embS P j T)]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarBlock]
  · rw [← padInto_zero (monitorDim P j T) (embS P j T)]; congr 1; ext a b
    fin_cases a <;> fin_cases b <;> simp [scalarBlock]
  · rw [← padInto_zero (monitorDim P j T) (embJ P j T), ← dilation_zero]; congr 2
  · rw [← padInto_zero (monitorDim P j T) (embL P j T), ← dilation_zero]; congr 2
    ext a b; simp [S45.pullback]

/-- The monitored value of the trial records of a sequence over a step set `K`. -/
def recMon (i : Fin (monitorCount P j T)) (x : RunRecord d m) (c : S45.Sequence (Port d m))
    (K : Finset ℕ) : S45.CMat (Fin (monitorDim P j T)) :=
  monitorOf P j T i
    (c.lagRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) K)
    (c.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) Finset.univ K)
    (c.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) S45.reserves K)
    (c.Jrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) K)
    (c.Lrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) K)

/-- The monitored value of one step. -/
def stepMon (i : Fin (monitorCount P j T)) (x : RunRecord d m) (c : S45.Sequence (Port d m))
    (k : ℕ) : S45.CMat (Fin (monitorDim P j T)) :=
  monitorOf P j T i
    (c.stepLag (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) k)
    (c.stepRow (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) Finset.univ k)
    (c.stepRow (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) S45.reserves k)
    (c.stepJ (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) k)
    (c.stepL (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) k)

theorem recMon_eq_sum (i : Fin (monitorCount P j T)) (x : RunRecord d m)
    (c : S45.Sequence (Port d m)) (K : Finset ℕ) :
    recMon P j T i x c K = ∑ k ∈ K, stepMon P j T i x c k := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    simp only [recMon, S45.Sequence.lagRecord, S45.Sequence.rowRecord, S45.Sequence.Jrecord,
      S45.Sequence.Lrecord, Finset.sum_empty]
    exact monitorOf_zero P j T i
  | insert k K hk ih =>
    rw [Finset.sum_insert hk, ← ih]
    simp only [recMon, stepMon, S45.Sequence.lagRecord, S45.Sequence.rowRecord,
      S45.Sequence.Jrecord, S45.Sequence.Lrecord, Finset.sum_insert hk]
    exact monitorOf_add P j T i _ _ _ _ _ _ _ _ _ _

/-- Earlier steps of the candidate are those of the prefix. -/
theorem stepMon_candidate (i : Fin (monitorCount P j T)) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (y : Torus d m) (ξ : ℝ) (k : ℕ) (hk : k < q.length) :
    stepMon P j T i x (candidate P j x q y ξ) k = stepMon P j T i x q k := by
  have h1 : k ≠ q.length + 1 := by omega
  have h2 : k + 1 ≠ q.length + 1 := by omega
  have h3 : k ≠ q.length := by omega
  simp only [stepMon]
  congr 1
  · funext p
    unfold S45.Sequence.stepLag
    unfold candidate extendSeq
    simp [h1, h2, h3]
  · funext p
    unfold S45.Sequence.stepRow
    unfold candidate extendSeq
    simp [h1, h2, h3]
  · funext p
    unfold S45.Sequence.stepRow
    unfold candidate extendSeq
    simp [h1, h2, h3]
  · unfold S45.Sequence.stepJ
    unfold candidate extendSeq
    simp [h1, h2, h3]
  · unfold S45.Sequence.stepL
    unfold candidate extendSeq
    simp [h1, h2, h3]

open Classical in
theorem tileEval_eq (x : RunRecord d m) (i : Fin (monitorCount P j T)) (k : ℕ)
    (ω : RandomSources (Torus d m) M) (y : Torus d m) (z : ℝ) :
    tileEval P j T M x i k ω (siteRank d m y) z =
      if activeIn P j T x y ∧ ((y, false) : Port d m) ∈
          (((slotSeq P j T M x k ω).getD x.sweep).state
            ((slotSeq P j T M x k ω).getD x.sweep).length).live then
        stepMon P j T i x (candidate P j x ((slotSeq P j T M x k ω).getD x.sweep) y z)
          ((slotSeq P j T M x k ω).getD x.sweep).length
      else 0 := by
  simp only [tileEval, Equiv.symm_apply_apply]
  rfl

/-- One accepted step: the records of the candidate are those of the prefix plus the step. -/
theorem recMon_candidate (i : Fin (monitorCount P j T)) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (y : Torus d m) (ξ : ℝ) (a : ℕ) (ha : a ≤ q.length) :
    recMon P j T i x q (Finset.Ico a q.length) +
        stepMon P j T i x (candidate P j x q y ξ) q.length =
      recMon P j T i x (candidate P j x q y ξ)
        (Finset.Ico a (candidate P j x q y ξ).length) := by
  have hlen : (candidate P j x q y ξ).length = q.length + 1 := rfl
  have hs : ∑ k ∈ Finset.Ico a q.length, stepMon P j T i x (candidate P j x q y ξ) k =
      ∑ k ∈ Finset.Ico a q.length, stepMon P j T i x q k :=
    Finset.sum_congr rfl fun k hk =>
      stepMon_candidate P j T i x q y ξ k (Finset.mem_Ico.mp hk).2
  rw [recMon_eq_sum, recMon_eq_sum, hlen, Finset.sum_Ico_succ_top ha, hs]

theorem slotSeq_succ (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) :
    slotSeq P j T M x (k + 1) ω = if k < slotCount P j T then
      (slotSeq P j T M x k ω).bind fun q =>
        slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)
    else slotSeq P j T M x k ω := rfl

open Classical in
theorem slotStep_eq (x : RunRecord d m) (q : S45.Sequence (Port d m)) (y : Torus d m) (ξ : ℝ) :
    slotStep P j T x q y ξ =
      if activeIn P j T x y ∧ ((y, false) : Port d m) ∈ (q.state q.length).live then
        (if trialOk P j T x (candidate P j x q y ξ)
            (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (q.state q.length)
              (y, false) ξ)
          then some (candidate P j x q y ξ) else none)
      else some q := by
  unfold slotStep; congr

/-- **Partial sums of the stopped monitored records** along the slot recursion. -/
theorem partialSum_tileRaw (x : RunRecord d m) (i : Fin (monitorCount P j T))
    (ω : RandomSources (Torus d m) M) :
    ∀ k q, slotSeq P j T M x k ω = some q → x.sweep.length ≤ q.length ∧
      S45.partialSum (tileRaw P j T M x i) k ω =
        recMon P j T i x q (Finset.Ico x.sweep.length q.length) := by
  intro k
  induction k with
  | zero =>
    intro q hq
    simp only [slotSeq, Option.some.injEq] at hq
    subst hq
    refine ⟨le_rfl, ?_⟩
    rw [recMon_eq_sum]
    simp [S45.partialSum]
  | succ k ih =>
    intro q hq
    rw [slotSeq_succ] at hq
    have hsum : S45.partialSum (tileRaw P j T M x i) (k + 1) ω =
        S45.partialSum (tileRaw P j T M x i) k ω + tileRaw P j T M x i (k + 1) ω := by
      simp only [S45.partialSum]; rw [Finset.sum_range_succ]
    rw [hsum]
    by_cases hk : k < slotCount P j T
    · rw [if_pos hk] at hq
      obtain ⟨q0, h0, hstep⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨hlen0, hps0⟩ := ih q0 h0
      have hrun : tileRun P j T M x k ω = true := by simp [tileRun, h0]
      have hraw : tileRaw P j T M x i (k + 1) ω = tileEval P j T M x i k ω
          (siteRank d m (tileSlot P j T M k ω)) (tileXi P j T M x k ω) := by
        simp only [tileRaw, hk, hrun, and_self, if_true]; rfl
      rw [hraw, tileEval_eq, h0, hps0]
      simp only [Option.getD_some]
      rw [slotStep_eq] at hstep
      by_cases hal : activeIn P j T x (tileSlot P j T M k ω) ∧
          ((tileSlot P j T M k ω, false) : Port d m) ∈ (q0.state q0.length).live
      · rw [if_pos hal] at hstep ⊢
        split_ifs at hstep with hok
        cases hstep
        exact ⟨by simp [candidate, extendSeq]; omega, recMon_candidate P j T i x q0 _ _ _ hlen0⟩
      · rw [if_neg hal] at hstep ⊢
        cases hstep
        exact ⟨hlen0, by simp⟩
    · rw [if_neg hk] at hq
      obtain ⟨hlen, hps⟩ := ih q hq
      refine ⟨hlen, ?_⟩
      rw [hps]
      simp [tileRaw, hk]

/-- The first failing slot. -/
theorem first_failure (x : RunRecord d m) (ω : RandomSources (Torus d m) M) :
    ∀ n, slotSeq P j T M x n ω = none → ∃ k < slotCount P j T, ∃ q,
      slotSeq P j T M x k ω = some q ∧
        slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω) = none := by
  intro n
  induction n with
  | zero => intro h; simp [slotSeq] at h
  | succ n ih =>
    intro h
    rcases hn : slotSeq P j T M x n ω with _ | q
    · exact ih hn
    · rw [slotSeq_succ] at h
      by_cases hk : n < slotCount P j T
      · rw [if_pos hk, hn] at h
        exact ⟨n, hk, q, hn, by simpa using h⟩
      · rw [if_neg hk, hn] at h; cases h

end Mon

/-- **A3 from A3b.** -/
theorem tileFailCrossing_of_transfer (d : ℕ) (C : ℝ) (h : TileTransferStatement d C) :
    TileFailCrossingStatement d C := by
  obtain ⟨t0, ht0, h⟩ := h
  refine ⟨t0, ht0, ?_⟩
  intro m P j T M x hu hj hjm hM hab hx ht ω hfail
  obtain ⟨k, hkN, q, hq, hstep⟩ := first_failure P j T M x ω _ hfail
  set y := tileSlot P j T M k ω with hy
  set ξ := tileXi P j T M x k ω with hξ
  set c := candidate P j x q y ξ with hc
  set t := sweepScale P.u m j with ht_def
  set r := portR (sweepTheta P.u m j) x.r with hr
  set K := Finset.Ico x.sweep.length c.length with hK
  rw [slotStep_eq] at hstep
  have hal : activeIn P j T x y ∧ ((y, false) : Port d m) ∈ (q.state q.length).live := by
    by_contra hn; rw [if_neg hn] at hstep; cases hstep
  rw [if_pos hal] at hstep
  have hnot : ¬ trialOk P j T x c (stepDen t r (q.state q.length) (y, false) ξ) := by
    intro hok; rw [if_pos hok] at hstep; cases hstep
  have hbud : ¬ S45.localBudget (P.cover j).cover T (c.Jrecord t r K) (c.Lrecord t r K)
      (c.lagRecord t r K) (c.rowRecord t r Finset.univ K) (c.rowRecord t r S45.reserves K) := by
    intro hb
    obtain ⟨hden, hval⟩ := h m P j T M x hu hj hjm hM hab hx ht k ω q hkN hq hal.1 hal.2 hb
    exact hnot ⟨hden, hval, hb⟩
  -- the partial sums at slot `k + 1`
  have hps : ∀ i, S45.partialSum (tileRaw P j T M x i) (k + 1) ω = recMon P j T i x c K := by
    intro i
    obtain ⟨hlen, hps0⟩ := partialSum_tileRaw P j T M x i ω k q hq
    have hrun : tileRun P j T M x k ω = true := by simp [tileRun, hq]
    have hraw : tileRaw P j T M x i (k + 1) ω = tileEval P j T M x i k ω
        (siteRank d m (tileSlot P j T M k ω)) (tileXi P j T M x k ω) := by
      simp only [tileRaw, hkN, hrun, and_self, if_true]; rfl
    simp only [S45.partialSum] at hps0 ⊢
    rw [Finset.sum_range_succ, hps0, hraw, tileEval_eq, hq]
    simp only [Option.getD_some]
    rw [if_pos hal]
    exact recMon_candidate P j T i x q y ξ _ hlen
  set n := (innerPorts P j T).card with hn
  have hcount : monitorCount P j T = 3 * n + 2 := rfl
  -- the four budget clauses
  unfold S45.localBudget at hbud
  by_cases hA : ∀ p ∈ (P.cover j).cover.inner T,
      ‖c.lagRecord t r K p‖ ≤ S45.power t (11 * S45.delta / 25)
  · by_cases hB : ∀ p ∈ (P.cover j).cover.inner T,
        |c.rowRecord t r Finset.univ K p| ≤ S45.power t (S45.delta / 2000) ∧
        |c.rowRecord t r S45.reserves K p| ≤ S45.power t (S45.delta / 2000)
    · by_cases hC : ‖S45.mask ((P.cover j).cover.inner T) (c.Jrecord t r K)‖ ≤
          S45.power t (S45.delta / 8)
      · -- the `L` monitor
        have hD : S45.power t (S45.delta / 8) <
            ‖S45.pullback ((P.cover j).cover.coords T).B (c.Lrecord t r K)‖ := by
          by_contra hD; exact hbud ⟨hA, hB, hC, not_lt.mp hD⟩
        refine ⟨⟨3 * n + 1, by omega⟩, k + 1, ?_⟩
        have h1 : ¬ (3 * n + 1 < n) := by omega
        have h2 : ¬ (3 * n + 1 < 2 * n) := by omega
        have h3 : ¬ (3 * n + 1 < 3 * n) := by omega
        have h4 : ¬ (3 * n + 1 = 3 * n) := by omega
        rw [hps]
        simp only [recMon, monitorOf, monitorKind, ← hn, dif_neg h1, dif_neg h2, dif_neg h3,
          if_neg h4, if_neg h1, if_neg h3]
        simp only [S45.monitorBudget]
        refine lt_of_lt_of_le hD ?_
        refine (real_le_complex _).trans ?_
        rw [← dilation_norm]
        exact padInto_norm_ge _ _ (embL_injective P j T) _
      · -- the `J` monitor
        refine ⟨⟨3 * n, by omega⟩, k + 1, ?_⟩
        have h1 : ¬ (3 * n < n) ∨ n = 0 := by omega
        rw [hps]
        by_cases hn0 : n = 0
        · have h1' : ¬ (3 * n < n) := by omega
          have h2 : ¬ (3 * n < 2 * n) := by omega
          have h3 : ¬ (3 * n < 3 * n) := by omega
          simp only [recMon, monitorOf, monitorKind, ← hn, dif_neg h1', dif_neg h2, dif_neg h3,
            if_true, if_neg h1', if_neg h3, S45.monitorBudget]
          refine lt_of_lt_of_le (not_le.mp hC) ?_
          refine (mask_norm_le _ _).trans ?_
          rw [← dilation_norm]
          exact padInto_norm_ge _ _ (embJ_injective P j T) _
        · have h1' : ¬ (3 * n < n) := by omega
          have h2 : ¬ (3 * n < 2 * n) := by omega
          have h3 : ¬ (3 * n < 3 * n) := by omega
          simp only [recMon, monitorOf, monitorKind, ← hn, dif_neg h1', dif_neg h2, dif_neg h3,
            if_true, if_neg h1', if_neg h3, S45.monitorBudget]
          refine lt_of_lt_of_le (not_le.mp hC) ?_
          refine (mask_norm_le _ _).trans ?_
          rw [← dilation_norm]
          exact padInto_norm_ge _ _ (embJ_injective P j T) _
    · -- a row monitor
      push_neg at hB
      obtain ⟨p, hp, hpb⟩ := hB
      set e := ((innerPorts P j T).equivFin ⟨p, hp⟩ : ℕ) with he
      have hel : e < n := ((innerPorts P j T).equivFin ⟨p, hp⟩).isLt
      have hsymm : ∀ (h : e < n), (innerPorts P j T).equivFin.symm ⟨e, h⟩ = ⟨p, hp⟩ := by
        intro h
        have he' : (⟨e, h⟩ : Fin n) = (innerPorts P j T).equivFin ⟨p, hp⟩ := Fin.ext rfl
        rw [he', Equiv.symm_apply_apply]
      by_cases hRa : |c.rowRecord t r Finset.univ K p| ≤ S45.power t (S45.delta / 2000)
      · have hRr := hpb hRa
        refine ⟨⟨2 * n + e, by omega⟩, k + 1, ?_⟩
        have h1 : ¬ (2 * n + e < n) := by omega
        have h2 : ¬ (2 * n + e < 2 * n) := by omega
        have h3 : 2 * n + e < 3 * n := by omega
        have hidx : (⟨2 * n + e - 2 * n, by omega⟩ : Fin n) = ⟨e, hel⟩ :=
          Fin.ext (show 2 * n + e - 2 * n = e by omega)
        rw [hps]
        simp only [recMon, monitorOf, monitorKind, ← hn, dif_neg h1, dif_neg h2, dif_pos h3,
          if_neg h1, if_pos h3, S45.monitorBudget]
        rw [show (⟨2 * n + e - 2 * n, _⟩ : Fin n) = ⟨e, hel⟩ from hidx, hsymm hel]
        exact lt_of_lt_of_le hRr ((scalarBlock_norm_ge _).trans
          (padInto_norm_ge _ _ (embS_injective P j T) _))
      · refine ⟨⟨n + e, by omega⟩, k + 1, ?_⟩
        have h1 : ¬ (n + e < n) := by omega
        have h2 : n + e < 2 * n := by omega
        have h3 : n + e < 3 * n := by omega
        have hidx : (⟨n + e - n, by omega⟩ : Fin n) = ⟨e, hel⟩ :=
          Fin.ext (show n + e - n = e by omega)
        rw [hps]
        simp only [recMon, monitorOf, monitorKind, ← hn, dif_neg h1, dif_pos h2,
          if_neg h1, if_pos h3, S45.monitorBudget]
        rw [show (⟨n + e - n, _⟩ : Fin n) = ⟨e, hel⟩ from hidx, hsymm hel]
        exact lt_of_lt_of_le (not_le.mp hRa) ((scalarBlock_norm_ge _).trans
          (padInto_norm_ge _ _ (embS_injective P j T) _))
  · -- a lag monitor
    push_neg at hA
    obtain ⟨p, hp, hpb⟩ := hA
    set e := ((innerPorts P j T).equivFin ⟨p, hp⟩ : ℕ) with he
    have hel : e < n := ((innerPorts P j T).equivFin ⟨p, hp⟩).isLt
    have hsymm : (innerPorts P j T).equivFin.symm ⟨e, hel⟩ = ⟨p, hp⟩ := by
      have he' : (⟨e, hel⟩ : Fin n) = (innerPorts P j T).equivFin ⟨p, hp⟩ := Fin.ext rfl
      rw [he', Equiv.symm_apply_apply]
    refine ⟨⟨e, by omega⟩, k + 1, ?_⟩
    rw [hps]
    simp only [recMon, monitorOf, monitorKind, ← hn, dif_pos hel, if_pos hel, S45.monitorBudget]
    rw [hsymm]
    exact lt_of_lt_of_le hpb ((scalarDilation_norm_ge _).trans
      (padInto_norm_ge _ _ (embS_injective P j T) _))

end AndersonAC.AgentS78
