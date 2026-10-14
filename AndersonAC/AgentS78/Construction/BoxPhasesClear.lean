import AndersonAC.AgentS78.Construction.BoxPhasesStage
import AndersonAC.AgentS78.Construction.StagePhaseSnoc
import AndersonAC.AgentS78.Construction.Exceptional
import AndersonAC.AgentS78.Construction.TrueValues

/-!
# the clearing operations

`boxCL_clearOp`: the clearing operation `(j, 2, y)` (`j ≤ ⌊m/2⌋`) keeps the clearing-phase set
`boxCL … Xc j = ClearPhase ∩ Damp ∩ PhysSet ∩ Xc j`, from

* `clear_exit_cases` (proved): the exit keeps `r` and the abort flag, and either keeps the
  endpoint and the installed values (aborted, unscheduled, empty core, FAIL, unfinished) or is
  the DONE exit `clearingDoneExit x sc`;
* `ClearPhase.of_exit` with the DONE step facts;
* two per-box inputs of the clearing package: the DONE step (`ClearingStepFacts` of the committed
  endpoint and the physical identity of the DONE record) and the record part `Xc j`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-- **The exits of the clearing block.** -/
theorem clear_exit_cases (n₀ j : ℕ) (u : ℝ) (yy : Torus d m) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m) (hs : BlockReach (clearingBlock n₀ j u yy) x s) :
    ((clearingBlock n₀ j u yy).exit s).r = x.r ∧
      ((clearingBlock n₀ j u yy).exit s).aborted = x.aborted ∧
      ((((clearingBlock n₀ j u yy).exit s).endpoint = x.endpoint ∧
          ((clearingBlock n₀ j u yy).exit s).installed = x.installed) ∨
        (x.aborted = false ∧ s.2.core ≠ ∅ ∧ s.2.failed = false ∧ s.2.done = true ∧
          (clearingBlock n₀ j u yy).exit s = clearingDoneExit x s.2)) := by
  classical
  obtain ⟨h1, -, -⟩ := clear_reach n₀ j u yy x s hs
  obtain ⟨r, sc⟩ := s
  simp only at h1
  subst h1
  have hex : (clearingBlock n₀ j u yy).exit (r, sc) = clearingExit j yy (r, sc) := rfl
  rw [hex]
  unfold clearingExit
  simp only
  split_ifs with ha hsch hcore hfail hdone
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨rfl, rfl, Or.inr ⟨by simpa using ha, hcore, by simpa using hfail, hdone, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

section Box
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ)
  (Cb CA cA PA cP CP : ℝ) (Xg : ℕ → Set (RunRecord d m)) (Xc : ℕ → ℕ → Set (RunRecord d m))

/-- **The clearing operation keeps the clearing-phase set.** -/
theorem boxCL_clearOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m / 2)
    (hdone : ∀ (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m),
      x ∈ RunBasics P (opIndex d m j 2 y) ∩ Xg (opIndex d m j 2 y) →
      x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y) → x.aborted = false →
      BlockReach (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x s →
      s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
      ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x s.2) ∧
        PhysicalIdentity E (clearingDoneExit x s.2))
    (hXc : OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y)) (Xc j (siteRank d m y + 1))) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y))
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y + 1)) := by
  intro x k ω hxRB hx hrun hh hexRB
  have hXcx := hXc x k ω hxRB hx hrun hh hexRB
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 2 y =
      (clearingBlock (d := d) (m := m) P.n₀ j P.u y).embed (clearEmbed ts₀) clearProj := by
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩),
      if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num),
      if_pos (show (2 : ℕ) = 2 from rfl), if_pos hjm]
  rw [hop] at hrun hXcx ⊢
  have hrun' : ∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) =
        false := by
    intro k' hk'
    have := hrun k' hk'
    rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
    exact this
  rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hXcx ⊢
  set s := localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω
    with hsdef
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
  change (clearingBlock (d := d) (m := m) P.n₀ j P.u y).exit s ∈ _
  change (clearingBlock (d := d) (m := m) P.n₀ j P.u y).exit s ∈ Xc j (siteRank d m y + 1) at hXcx
  obtain ⟨hr, hab, hcases⟩ := clear_exit_cases P.n₀ j P.u y x s hreach
  have hx0 := hx
  obtain ⟨⟨⟨hCP, hD⟩, hPh⟩, -⟩ := hx
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hXcx⟩
  · show ClearPhase P.n₀ P.u E ρ Cb CA cA PA j _
    rcases hcases with ⟨he, -⟩ | ⟨hxab, hc, hf, hdn, hdeq⟩
    · exact ClearPhase.transfer hCP (fun h => hab ▸ h) (fun _ => ⟨he, hr⟩)
    · rw [hdeq]
      exact (hdone x s hxRB hx0 hxab hreach hc hf hdn).1
  · intro i; rw [hr]; exact hD i
  · intro hab'
    rcases hcases with ⟨he, hi⟩ | ⟨hxab, hc, hf, hdn, hdeq⟩
    · exact physicalIdentity_congr he.symm hi.symm (hPh (hab ▸ hab'))
    · rw [hdeq]
      exact (hdone x s hxRB hx0 hxab hreach hc hf hdn).2

/-- **The clearing operation keeps the clearing-phase set** off the exceptional set, for entering
records with true installed values (route R2). -/
theorem boxCL_clearOpZ (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m / 2)
    (hdone : ∀ (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P)),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      x ∈ TrueValues P.n₀ P.u ω →
      x ∈ RunBasics P (opIndex d m j 2 y) ∩ Xg (opIndex d m j 2 y) →
      x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y) → x.aborted = false →
      (∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) =
          false) →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.core
        ≠ ∅ →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.failed
        = false →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.done
        = true →
      ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2) ∧
        PhysicalIdentity E (clearingDoneExit x
          (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2))
    (hXc : OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y)) (Xc j (siteRank d m y + 1))) :
    OpKeepsZ P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n)
      (fun ω => {x | ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) ∧
        x ∈ TrueValues P.n₀ P.u ω}) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y))
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y + 1)) := by
  intro x k ω hG hxRB hx hrun hh hexRB
  have hXcx := hXc x k ω hxRB hx hrun hh hexRB
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 2 y =
      (clearingBlock (d := d) (m := m) P.n₀ j P.u y).embed (clearEmbed ts₀) clearProj := by
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩),
      if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num),
      if_pos (show (2 : ℕ) = 2 from rfl), if_pos hjm]
  rw [hop] at hrun hXcx ⊢
  have hrun' : ∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) =
        false := by
    intro k' hk'
    have := hrun k' hk'
    rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
    exact this
  rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hXcx ⊢
  set s := localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω
    with hsdef
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
  change (clearingBlock (d := d) (m := m) P.n₀ j P.u y).exit s ∈ _
  change (clearingBlock (d := d) (m := m) P.n₀ j P.u y).exit s ∈ Xc j (siteRank d m y + 1) at hXcx
  obtain ⟨hr, hab, hcases⟩ := clear_exit_cases P.n₀ j P.u y x s hreach
  have hx0 := hx
  obtain ⟨⟨⟨hCP, hD⟩, hPh⟩, -⟩ := hx
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hXcx⟩
  · show ClearPhase P.n₀ P.u E ρ Cb CA cA PA j _
    rcases hcases with ⟨he, -⟩ | ⟨hxab, hc, hf, hdn, hdeq⟩
    · exact ClearPhase.transfer hCP (fun h => hab ▸ h) (fun _ => ⟨he, hr⟩)
    · rw [hdeq]
      exact (hdone x k ω hG.1 hG.2 hxRB hx0 hxab hrun' hc hf hdn).1
  · intro i; rw [hr]; exact hD i
  · intro hab'
    rcases hcases with ⟨he, hi⟩ | ⟨hxab, hc, hf, hdn, hdeq⟩
    · exact physicalIdentity_congr he.symm hi.symm (hPh (hab ▸ hab'))
    · rw [hdeq]
      exact (hdone x k ω hG.1 hG.2 hxRB hx0 hxab hrun' hc hf hdn).2

/-- **The clearing operation of a non-clearing stage** (`⌊m/2⌋ < j ≤ m`) is the identity; it
keeps the clearing-phase set when the record part is monotone in the scan position there
(scan-position amendment). -/
theorem boxCL_clearId (j : ℕ) (y : Torus d m) (hjm : ¬ j ≤ m / 2)
    (hmono : ∀ r, Xc j r ⊆ Xc j (r + 1)) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y))
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y + 1)) := by
  intro x k ω _ hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 2 y = simpleBlock (ts₀, cl₀) id := by
    unfold runOp
    split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)
  rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 2 y id hop x k ω hrun]
  exact ⟨hx.1, hmono _ hx.2⟩

end Box

end AndersonAC.AgentS78
