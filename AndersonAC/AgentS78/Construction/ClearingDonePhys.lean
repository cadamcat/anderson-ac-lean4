import AndersonAC.AgentS78.Construction.SchurQuotient
import AndersonAC.AgentS78.Construction.StagePhaseClr
import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# The physical identity after a DONE clearing with regular pivots

02-state.tex:222–247 works on the event where every true principal block of `H − E` is invertible.
Pathwise, the clearing block (`clearingBlock`) eliminates its pivots one at a time by the scalar
Schur step `schurStepM` with the revealed residual `ξ` as diagonal shift. By the quotient formula
`B/(T ∪ {p}) = (B/T)/p` the provisional matrix `Mnum`, restricted to the provisional active set,
stays the Schur complement of the shifted installed values (`installed + resids`) onto that set,
provided every pivot is still active and nonzero and the eliminated block of the entering record
is invertible.

* `ClrStepRegular` — the scratch-level pivot predicate of one update: a heat pivot is still active
  and `Mnum p p + ξ ≠ 0`; a core pivot has `Mnum y y + ξ ≠ 0` (it is active by the core
  bookkeeping). Other actions impose nothing. This is the `x ∈ s.active` and `≠ 0` clause of
  `S6.HeatTransition`.
* `ClrRegReach` — `BlockReach` of the clearing block along regular updates only.
* `TerminalInvertible E x` — the eliminated block `(installedShifted E x)_{Aᶜ Aᶜ}` is invertible
  (`A = x.endpoint.active`). Needed: with the junk `⁻¹ = 0` of a singular block,
  `PhysicalIdentity E x` alone does not determine the quotient.
* **`clearingDonePhys_of_pivots`** — along `ClrRegReach` ending in DONE,
  `PhysicalIdentity ∧ TerminalInvertible` passes from `x` to `clearingDoneExit x s.2`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Answer)

variable {d m : ℕ}

/-- **Regular elimination step** of the clearing block at `s` with answer `a`. -/
def ClrStepRegular (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) : Prop :=
  match actionOf (d := d) (m := m) j u s.1 s.2 with
  | .heat p _ => p ∈ s.2.active ∧
      s.2.Mnum p p + residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p (s.1.prefixLength p) a ≠ 0
  | .coreQuery y _ =>
      s.2.Mnum y y + (residOfAnswer (d := d) (m := m) (clearingLam n₀ u) y 0 a - s.1.installed y) ≠ 0
  | _ => True

/-- **Reachable states of the clearing block along regular steps.** -/
inductive ClrRegReach (n₀ j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m) :
    RunRecord d m × ClearScratch d m → Prop
  | enter : ClrRegReach n₀ j u y x ((clearingBlock (d := d) (m := m) n₀ j u y).enter x)
  | step (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m)) :
      ClrRegReach n₀ j u y x s → (clearingBlock (d := d) (m := m) n₀ j u y).halted s = false →
      ClrStepRegular (d := d) (m := m) n₀ j u s a →
      ClrRegReach n₀ j u y x ((clearingBlock (d := d) (m := m) n₀ j u y).update s a)

theorem ClrRegReach.blockReach {n₀ j : ℕ} {u : ℝ} {y : Torus d m} {x : RunRecord d m}
    {s : RunRecord d m × ClearScratch d m} (h : ClrRegReach n₀ j u y x s) :
    BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s := by
  induction h with
  | enter => exact BlockReach.enter
  | step s a _ hh _ ih => exact BlockReach.step s a ih hh

/-- **The eliminated block of a record is invertible.** -/
def TerminalInvertible (E : ℝ) (x : RunRecord d m) : Prop :=
  IsUnit (offBlock (installedShifted E x) x.endpoint.active).det

/-! ## The Schur invariant along the block -/

/-- The shifted installed values of the entering record plus the provisional residuals. -/
def scratchShifted (E : ℝ) (x : RunRecord d m) (sc : ClearScratch d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  installedShifted E x + Matrix.diagonal (fun i => ((sc.resids i : ℝ) : ℂ))

/-- The provisional matrix as a complex matrix. -/
def mnumC (sc : ClearScratch d m) : Matrix (Torus d m) (Torus d m) ℂ :=
  fun i k => ((sc.Mnum i k : ℝ) : ℂ)

/-- **The Schur invariant of a reachable clearing scratch state** (entering record `x`). -/
structure SchurInv (j : ℕ) (E : ℝ) (x : RunRecord d m) (sc : ClearScratch d m) : Prop where
  pre : sc.corePhase = false → sc.coreLeft = sc.core
  post : sc.corePhase = true → sc.core ∩ sc.active = sc.coreLeft
  done : sc.done = true → sc.failed = false → x.aborted = false → clearingScheduled j m →
    sc.core ≠ ∅ → sc.corePhase = true ∧ sc.coreLeft = ∅
  residA : ∀ i ∈ sc.active, sc.resids i = 0
  residS : ∀ i, sc.resids i ≠ 0 → i ∈ sc.core ∪ sc.inspected
  sub : sc.active ⊆ x.endpoint.active
  residX : ∀ i, sc.resids i ≠ 0 → i ∈ x.endpoint.active
  phys : sc.failed = false → SchurRel (scratchShifted E x sc) sc.active (mnumC sc) ∧
    OffInj (scratchShifted E x sc) sc.active

theorem schurRel_congr {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    {A : Finset ι} {S S' : Matrix ι ι ℂ} (h : SchurRel B A S)
    (hS : ∀ i ∈ A, ∀ k ∈ A, S i k = S' i k) : SchurRel B A S' := by
  intro v
  obtain ⟨x, hx, hT, hA⟩ := h v
  refine ⟨x, hx, hT, fun i hi => ?_⟩
  rw [hA i hi]
  exact Finset.sum_congr rfl (fun k hk => by rw [hS i hi k hk])

/-- The installed shifted matrix is real. -/
theorem installedShifted_conj (E : ℝ) (x : RunRecord d m) (i k : Torus d m) :
    (starRingEnd ℂ) (installedShifted E x i k) = installedShifted E x i k := by
  rw [Complex.conj_eq_iff_im]
  simp only [installedShifted, OAI.Anderson.periodicHamiltonian, Matrix.sub_apply,
    Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.im_sum, Complex.mul_im,
    apply_ite Complex.im, apply_ite Complex.re, Complex.one_im, Complex.zero_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.one_re, Complex.zero_re, ite_self, add_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, neg_zero, sub_zero]

/-- One elimination with a nonzero pivot keeps the Schur clause. -/
theorem schurInv_elim (E : ℝ) (x : RunRecord d m) (sc sc' : ClearScratch d m) (p : Torus d m)
    (ξ : ℝ) (hp : p ∈ sc.active) (hpiv : sc.Mnum p p + ξ ≠ 0) (hres : sc.resids p = 0)
    (hS : SchurRel (scratchShifted E x sc) sc.active (mnumC sc))
    (hI : OffInj (scratchShifted E x sc) sc.active)
    (hM : sc'.Mnum = schurStepM sc.Mnum p ξ) (hA : sc'.active = sc.active.erase p)
    (hR : sc'.resids = Function.update sc.resids p ξ) :
    SchurRel (scratchShifted E x sc') sc'.active (mnumC sc') ∧
      OffInj (scratchShifted E x sc') sc'.active := by
  have hB : scratchShifted E x sc' =
      scratchShifted E x sc + Matrix.diagonal (Pi.single p (ξ : ℂ) : Torus d m → ℂ) := by
    unfold scratchShifted
    rw [add_assoc, Matrix.diagonal_add, hR]
    congr 2
    funext i
    by_cases hip : i = p
    · subst hip; simp [hres]
    · simp [hip]
  have hMc : mnumC sc' = schurStepK (mnumC sc) p (ξ : ℂ) := by
    funext i k
    simp only [mnumC, hM, schurStepM, schurStepK]
    split_ifs <;> push_cast <;> rfl
  have hpivC : mnumC sc p p + (ξ : ℂ) ≠ 0 := by
    simp only [mnumC]; exact_mod_cast hpiv
  rw [hB, hMc, hA]
  exact ⟨schurRel_step hS hp _ hpivC, offInj_step hS hI hp _ hpivC⟩

/-- A heat elimination keeps the invariant. -/
theorem schurInv_heat {j : ℕ} {E : ℝ} {x : RunRecord d m} (sc sc' : ClearScratch d m)
    (p : Torus d m) (ξ : ℝ) (hI : SchurInv j E x sc) (hf : sc.failed = false)
    (hd : sc'.done = false) (hp : p ∈ sc.active) (hpc : p ∉ sc.core)
    (hsub : sc.core ⊆ sc.active) (hcp : sc.corePhase = false) (hpiv : sc.Mnum p p + ξ ≠ 0)
    (hM : sc'.Mnum = schurStepM sc.Mnum p ξ) (hA : sc'.active = sc.active.erase p)
    (hR : sc'.resids = Function.update sc.resids p ξ) (hC : sc'.core = sc.core)
    (hL : sc'.coreLeft = sc.coreLeft) (hIn : sc'.inspected = insert p sc.inspected) :
    SchurInv j E x sc' where
  pre := fun _ => by rw [hL, hC, hI.pre hcp]
  sub := by rw [hA]; exact (Finset.erase_subset _ _).trans hI.sub
  residX := fun i hi => by
    by_cases hip : i = p
    · subst hip; exact hI.sub hp
    · rw [hR, Function.update_of_ne hip] at hi
      exact hI.residX i hi
  post := fun _ => by
    rw [hA, hC, hL, hI.pre hcp, Finset.inter_eq_left]
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun h => hpc (h ▸ hz), hsub hz⟩
  done := fun h => by rw [hd] at h; cases h
  residA := fun i hi => by
    rw [hA] at hi
    rw [hR, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    exact hI.residA i (Finset.mem_of_mem_erase hi)
  residS := fun i hi => by
    rw [hC, hIn]
    by_cases hip : i = p
    · subst hip; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · rw [hR, Function.update_of_ne hip] at hi
      rcases Finset.mem_union.mp (hI.residS i hi) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
  phys := fun _ => schurInv_elim E x sc sc' p ξ hp hpiv (hI.residA p hp) (hI.phys hf).1
    (hI.phys hf).2 hM hA hR

/-- **One regular update keeps the invariant.** -/
theorem schurInv_update (n₀ j : ℕ) (u E : ℝ) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m)) (hx : s.1 = x)
    (hreg : ClrStepRegular (d := d) (m := m) n₀ j u s a) (hI : SchurInv j E x s.2) :
    SchurInv j E x (clearingUpdate (d := d) (m := m) n₀ j u s a).2 := by
  subst hx
  unfold ClrStepRegular at hreg
  unfold clearingUpdate
  dsimp only
  split
  · exact hI
  rename_i hnot
  have hf : s.2.failed = false := by simpa using (not_or.mp hnot).1
  have hd : s.2.done = false := by simpa using (not_or.mp hnot).2
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po =>
    refine { hI with residS := fun i hi => ?_, phys := fun h => by simp at h, done := fun _ h => by simp at h }
    rcases Finset.mem_union.mp (hI.residS i hi) with h | h
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      cases po with
      | none => exact h
      | some p => exact Finset.mem_insert_of_mem h
  | coreReady =>
    obtain ⟨hcp, hsub⟩ := actionOf_coreReady_facts j u s.1 s.2 hact
    refine { hI with
      pre := fun h => by simp at h
      post := fun _ => ?_
      done := fun h => by simp [hd] at h }
    show s.2.core ∩ s.2.active = s.2.coreLeft
    rw [Finset.inter_eq_left.mpr hsub, hI.pre hcp]
  | finish =>
    refine { hI with done := fun _ _ _ _ hne => ?_ }
    exact actionOf_finish_facts j u s.1 s.2 hf hd hne hact
  | coreQuery p hcp =>
    rw [hact] at hreg
    have hmem := actionOf_coreQuery_mem j u s.1 s.2 p hcp hact
    have hpost := hI.post hcp
    have hpa : p ∈ s.2.active := (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).2
    have hpc : p ∈ s.2.core := (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).1
    dsimp only
    refine
      { pre := ?_, post := ?_, done := ?_, residA := ?_, residS := ?_, sub := ?_,
        residX := ?_, phys := ?_ }
    · intro h; simp [hcp] at h
    · intro _
      show s.2.core ∩ s.2.active.erase p = s.2.coreLeft.erase p
      rw [← hpost, Finset.inter_erase]
    · intro hdn _ _ _ _
      refine ⟨hcp, ?_⟩
      simpa using hdn
    · intro i hi
      show Function.update s.2.resids p _ i = 0
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      exact hI.residA i (Finset.mem_of_mem_erase hi)
    · intro i hi
      by_cases hip : i = p
      · subst hip; exact Finset.mem_union_left _ hpc
      · exact hI.residS i (by
          have : Function.update s.2.resids p
            (residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p 0 a - s.1.installed p) i ≠ 0 := hi
          rwa [Function.update_of_ne hip] at this)
    · exact (Finset.erase_subset _ _).trans hI.sub
    · intro i hi
      by_cases hip : i = p
      · subst hip; exact hI.sub hpa
      · exact hI.residX i (by
          have : Function.update s.2.resids p
            (residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p 0 a - s.1.installed p) i ≠ 0 := hi
          rwa [Function.update_of_ne hip] at this)
    · intro _
      exact schurInv_elim E s.1 s.2 _ p _ hpa hreg (hI.residA p hpa) (hI.phys hf).1
        (hI.phys hf).2 rfl rfl rfl
  | heat p hg =>
    rw [hact] at hreg
    obtain ⟨hcp, hsub, hpc, _⟩ := actionOf_heat_facts j u s.1 s.2 p hg hact
    dsimp only
    split_ifs
    all_goals exact (schurInv_heat s.2 _ p _ hI hf hd hreg.1 hpc hsub hcp hreg.2
      rfl rfl rfl rfl rfl rfl)

/-- The invariant at entry. -/
theorem schurInv_enter (j : ℕ) (u E : ℝ) (y : Torus d m) (x : RunRecord d m)
    (hP : PhysicalIdentity E x) (hT : TerminalInvertible E x) :
    SchurInv j E x (clearInitScratch (d := d) (m := m) j u y x) := by
  have hI : OffInj (installedShifted E x) x.endpoint.active :=
    (offInj_iff_isUnit _ _).mpr hT
  have hS0 := schurRel_activeSchur (installedShifted E x) x.endpoint.active hI
  have hreal : ∀ i ∈ x.endpoint.active, ∀ k ∈ x.endpoint.active,
      (((padSchur (installedShifted E x) x.endpoint.active i k).re : ℝ) : ℂ) =
        padSchur (installedShifted E x) x.endpoint.active i k := by
    intro i hi k hk
    apply Complex.conj_eq_iff_re.mp
    exact (schurRel_unique (schurRel_conj (installedShifted_conj E x) hS0) hS0 hI hi hk)
  have hM : ∀ i ∈ x.endpoint.active, ∀ k ∈ x.endpoint.active,
      x.endpoint.M i k = padSchur (installedShifted E x) x.endpoint.active i k := by
    intro i hi k hk
    have := congrFun (congrFun hP ⟨i, hi⟩) ⟨k, hk⟩
    simp only [Matrix.submatrix_apply] at this
    rw [this]
    simp [padSchur, hi, hk]
  refine
    { pre := ?_, post := ?_, done := ?_, residA := ?_, residS := ?_, sub := ?_,
      residX := ?_, phys := ?_ }
  · intro _; rfl
  · intro h; simp [clearInitScratch] at h
  · intro hdone _ hab hsch hne
    exfalso
    simp only [clearInitScratch] at hdone hne
    simp [hab, hsch, hne] at hdone
  · intro i _; rfl
  · intro i hi; exact (hi rfl).elim
  · exact Finset.Subset.refl _
  · intro i hi; exact (hi rfl).elim
  · intro _
    have hB : scratchShifted E x (clearInitScratch (d := d) (m := m) j u y x) =
        installedShifted E x := by
      unfold scratchShifted
      simp [clearInitScratch]
    rw [hB]
    refine ⟨schurRel_congr hS0 (fun i hi k hk => ?_), hI⟩
    show _ = (((x.endpoint.M i k).re : ℝ) : ℂ)
    rw [hM i hi k hk, hreal i hi k hk]

/-- The invariant along every regular reach. -/
theorem schurInv_reach (n₀ j : ℕ) (u E : ℝ) (y : Torus d m) (x : RunRecord d m)
    (hP : PhysicalIdentity E x) (hT : TerminalInvertible E x)
    (s : RunRecord d m × ClearScratch d m) (h : ClrRegReach n₀ j u y x s) :
    SchurInv j E x s.2 := by
  induction h with
  | enter => exact schurInv_enter j u E y x hP hT
  | step s a hs _ hreg ih =>
    exact schurInv_update n₀ j u E x s a (clr_reach n₀ j u y x s hs.blockReach).1 hreg ih

/-- From the Schur relation of the committed data to the physical identity. -/
theorem physicalIdentity_of_schurRel (E : ℝ) (x' : RunRecord d m)
    (B : Matrix (Torus d m) (Torus d m) ℂ) (hB : installedShifted E x' = B)
    (hS : SchurRel B x'.endpoint.active x'.endpoint.M) (hI : OffInj B x'.endpoint.active) :
    PhysicalIdentity E x' ∧ TerminalInvertible E x' := by
  unfold PhysicalIdentity TerminalInvertible
  rw [hB]
  refine ⟨?_, (offInj_iff_isUnit _ _).mp hI⟩
  ext a b
  have := schurRel_unique hS (schurRel_activeSchur B _ hI) hI a.2 b.2
  rw [Matrix.submatrix_apply, this]
  simp [padSchur]

/-- **The step invariant at a regular reachable state** (export for): on the
provisional active set, `Mnum` is the Schur complement of the shifted installed values
(`installedShifted E x` plus the residuals on the sites eliminated so far), and the eliminated
block of that matrix is invertible. -/
theorem clrRegReach_schur {n₀ j : ℕ} {u E : ℝ} {y : Torus d m} {x : RunRecord d m}
    {s : RunRecord d m × ClearScratch d m} (hs : ClrRegReach n₀ j u y x s)
    (hP : PhysicalIdentity E x) (hT : TerminalInvertible E x) (hf : s.2.failed = false) :
    (∀ a b : s.2.active, ((s.2.Mnum a b : ℝ) : ℂ) =
      SolS78.activeSchur (scratchShifted E x s.2) s.2.active a b) ∧
    IsUnit (offBlock (scratchShifted E x s.2) s.2.active).det ∧
    scratchShifted E x s.2 = installedShifted E x + Matrix.diagonal (fun i =>
      if i ∈ x.endpoint.active \ s.2.active then ((s.2.resids i : ℝ) : ℂ) else 0) := by
  have hI := schurInv_reach n₀ j u E y x hP hT s hs
  obtain ⟨hS, hO⟩ := hI.phys hf
  refine ⟨fun a b => ?_, (offInj_iff_isUnit _ _).mp hO, ?_⟩
  · have := schurRel_unique hS (schurRel_activeSchur _ _ hO) hO a.2 b.2
    rw [show ((s.2.Mnum a b : ℝ) : ℂ) = mnumC s.2 a b from rfl, this]
    simp [padSchur]
  · unfold scratchShifted
    congr 2
    funext i
    by_cases h0 : s.2.resids i = 0
    · rw [h0]; simp
    · have hi : i ∈ x.endpoint.active \ s.2.active :=
        Finset.mem_sdiff.mpr ⟨hI.residX i h0, fun h => h0 (hI.residA i h)⟩
      rw [if_pos hi]

/-- **The pivot is nonzero when the enlarged eliminated block is invertible** (export for
on the event where the true principal blocks are invertible, this gives
`ClrStepRegular`'s `≠ 0` clause). -/
theorem clrRegReach_pivot_ne_zero {n₀ j : ℕ} {u E : ℝ} {y : Torus d m} {x : RunRecord d m}
    {s : RunRecord d m × ClearScratch d m} (hs : ClrRegReach n₀ j u y x s)
    (hP : PhysicalIdentity E x) (hT : TerminalInvertible E x) (hf : s.2.failed = false)
    {p : Torus d m} (hp : p ∈ s.2.active) (ξ : ℝ)
    (hdet : IsUnit (offBlock (scratchShifted E x s.2 +
      Matrix.diagonal (Pi.single p (ξ : ℂ) : Torus d m → ℂ)) (s.2.active.erase p)).det) :
    s.2.Mnum p p + ξ ≠ 0 := by
  have hI := schurInv_reach n₀ j u E y x hP hT s hs
  have h := pivot_ne_zero_of_offInj (hI.phys hf).1 hp (ξ : ℂ) ((offInj_iff_isUnit _ _).mpr hdet)
  intro h0
  apply h
  simp only [mnumC]
  exact_mod_cast h0

/-- ** (A): the physical identity after a DONE clearing with regular pivots.** -/
theorem clearingDonePhys_of_pivots (d : ℕ) :
    ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (y : Torus d m) (x : RunRecord d m)
      (s : RunRecord d m × ClearScratch d m),
      ClrRegReach n₀ j u y x s → x.aborted = false →
      clearingScheduled j m → s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      PhysicalIdentity E x → TerminalInvertible E x →
      PhysicalIdentity E (clearingDoneExit x s.2) ∧
        TerminalInvertible E (clearingDoneExit x s.2) := by
  intro m n₀ j u E y x s hs hab hsch hne hf hdn hP hT
  have hI := schurInv_reach n₀ j u E y x hP hT s hs
  obtain ⟨hcp, hleft⟩ := hI.done hdn hf hab hsch hne
  have hdisj : s.2.core ∩ s.2.active = ∅ := (hI.post hcp).trans hleft
  have hact : (clearingDoneExit x s.2).endpoint.active = s.2.active := by
    show s.2.active \ s.2.core = s.2.active
    rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm,
      hdisj]
  have hinst : ∀ i, (clearingDoneExit x s.2).installed i = x.installed i + s.2.resids i := by
    intro i
    show (if i ∈ s.2.core ∪ s.2.inspected then x.installed i + s.2.resids i
      else x.installed i) = _
    split_ifs with hi
    · rfl
    · by_cases h0 : s.2.resids i = 0
      · rw [h0, add_zero]
      · exact absurd (hI.residS i h0) hi
  have hB : installedShifted E (clearingDoneExit x s.2) = scratchShifted E x s.2 := by
    ext a b
    simp only [installedShifted, scratchShifted, hinst, Matrix.add_apply, Matrix.sub_apply,
      Matrix.diagonal_apply]
    split_ifs <;> push_cast <;> ring
  obtain ⟨hS, hO⟩ := hI.phys hf
  have hM : (clearingDoneExit x s.2).endpoint.M = mnumC s.2 := rfl
  apply physicalIdentity_of_schurRel E _ _ hB
  · rw [hact, hM]; exact hS
  · rw [hact]; exact hO

end AndersonAC.AgentS78
