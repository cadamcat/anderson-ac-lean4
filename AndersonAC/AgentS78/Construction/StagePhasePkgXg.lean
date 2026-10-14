import AndersonAC.AgentS78.Construction.StagePhasePkgClr

/-!
# Clearing-phase package: the run-level set is closed along the schedule. `pkgXg_closed` (`ClearingBoxFacts.hXg`): every block keeps
`pkgXg` (cover, pending ⊆ active, a trace whose edits are the terminal set) given `RunBasics` and,
at clearing indices, the clearing-phase set: tile blocks keep the endpoint and (off the final
sweep) the terminal set and only add active sites to the pending set (`tile_reach`); the sweep end
keeps the active set under `RunBasics` and the trace is read at the next index; clearing blocks
by `clearRecPos_fail` / `clearRecPos_done`; stage operations keep the fields
(`stageWith_fields`); all other blocks are the identity.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

theorem gIdx_some_J (P : TilePlan d m) (n k : ℕ) (h : gIdx P n = some k) :
    decodeJ d m n ≤ P.n₀ ∨ decodeJ d m n ≤ m := by
  unfold gIdx at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  all_goals first | exact Or.inr h2 | (simp at h)

theorem gIdx_clear (P : TilePlan d m) (n : ℕ) (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m)
    (hK : decodeK d m n = 2 ∨ decodeK d m n = 3) : gIdx P n = some (decodeJ d m n) := by
  unfold gIdx
  rw [if_neg (by omega), if_pos h2, if_neg (by omega)]

theorem gIdx_end (P : TilePlan d m) (n : ℕ) (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m)
    (hK : decodeK d m n = 1) (hR : n % siteCount d m = 0) :
    gIdx P n = some (decodeJ d m n - 1) := by
  unfold gIdx
  rw [if_neg (by omega), if_pos h2, if_pos (Or.inr ⟨hK, hR⟩)]

/-- **`Xg` is closed along every block** (`ClearingBoxFacts.hXg`). -/
theorem pkgXg_closed (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (E : ℝ) (ρ : ℂ) (Cb CA cA PA cB CB dlo dhi : ℝ) (hnm : P.n₀ < m) (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (hsmall4 : ∀ j, P.n₀ < j → stageScale P.u j m ≤ 1 / 4) :
    ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    x ∈ RunBasics P n ∩ pkgXg (2 ^ 25) P n →
    (∀ j r, boxPhase P n = .clear j r →
      x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA dlo dhi (pkgXc cB CB (2 ^ 25) P E ρ Cb CA cA PA) j r) →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
        false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
        true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
        pkgXg (2 ^ 25) P (n + 1) := by
  classical
  intro n x k ω hx hcl hrun hh hab' k' hk'
  have hK4 := decodeK_lt (d := d) (m := m) n
  have hYs := decodeY_eq_site₀_iff (d := d) (m := m) n
  have hRY := rank_decodeY (d := d) (m := m) n
  have hB : scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n =
      runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) := rfl
  rw [hB] at hrun hh hab' ⊢
  have hsimple : ∀ f : RunRecord d m → RunRecord d m,
      runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) =
        simpleBlock (ts₀, cl₀) f →
      (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n)).exit
        (localState (tileOrderSize P)
          (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n))
            x k ω) = f x := by
    intro f hf
    exact runOp_simple_exit P ts₀ cl₀ P.n₀ P.u _ _ _ f hf x k ω hrun
  -- the identity case
  have hid : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) =
      simpleBlock (ts₀, cl₀) id →
      ¬ (decodeK d m n = 1 ∧ n % siteCount d m = 0 ∧ P.n₀ < decodeJ d m n ∧
        decodeJ d m n ≤ m) →
      (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n)).exit
        (localState (tileOrderSize P)
          (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n))
            x k ω) ∈ {x' : RunRecord d m | x'.aborted = false →
              ∀ k', gIdx P (n + 1) = some k' → RunG (2 ^ 25) P.n₀ P.u k' x'} := by
    intro hf hnot hab'' k'' hk''
    rw [hsimple id hf] at hab'' ⊢
    rcases gIdx_succ P n k'' hk'' with hkeep | ⟨h1, h2, h3, h4, -, -⟩
    · exact hx.2 hab'' k'' hkeep
    · exact absurd ⟨h1, h2, h3, h4⟩ hnot
  by_cases hin : P.n₀ < decodeJ d m n ∧ decodeJ d m n ≤ m + 1
  swap
  · exact hid (by unfold runOp; rw [if_neg hin]) (fun h => hin ⟨h.2.2.1, by omega⟩) hab' k' hk'
  by_cases hk0 : decodeK d m n = 0
  · cases hT : tileAt P (decodeJ d m n) (decodeY d m n) with
    | none =>
      exact hid (by unfold runOp; rw [if_pos hin, if_pos hk0, hT]) (fun h => by omega) hab' k' hk'
    | some T =>
      have hrB : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n)
          (decodeY d m n) = (tileBlock P (decodeJ d m n) T).embed (tileEmbed cl₀) tileProj := by
        unfold runOp; rw [if_pos hin, if_pos hk0, hT]
      rw [hrB] at hrun hh hab' ⊢
      have hrun' : ∀ k' < k, (tileBlock P (decodeJ d m n) T).halted
          (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k' ω) = false := by
        intro k'' hk''
        have := hrun k'' hk''
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
        exact this
      have hh' : (tileBlock P (decodeJ d m n) T).halted
          (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k ω) = true := by
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hh
        exact hh
      rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hab' ⊢
      change (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k ω).1.aborted =
        false at hab'
      show RunG (2 ^ 25) P.n₀ P.u k'
        (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k ω).1
      have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
      have hab : x.aborted = false := by
        cases h : x.aborted
        · rfl
        · rw [tile_reach_aborted P _ T x h _ hreach, h] at hab'; cases hab'
      have hE := (tile_reach P _ T x hab _ hreach).2 hh' hab'
      rcases gIdx_succ P n k' hk' with hkeep | ⟨h1, -⟩
      swap
      · omega
      have hJm : decodeJ d m n ≤ m := (gIdx_some_J P n k' hkeep).resolve_left (by omega)
      have hG := hx.2 hab k' hkeep
      refine runG_of_fields hG (by rw [hE.ep]) (TExitOK.term_off P _ T x hE
        (by unfold IsFinalSweep; omega)) ?_
      rcases hE.out with ⟨hp, -⟩ | ⟨-, hp, -⟩
      · rw [hp]; exact Finset.subset_union_left
      · rw [hp]
        exact Finset.union_subset_union (Finset.Subset.refl _) Finset.inter_subset_right
  by_cases hk1 : decodeK d m n = 1
  · by_cases hy : decodeY d m n = site₀ d m
    · have hR0 : n % siteCount d m = 0 := hYs.mp hy
      have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n)
          (decodeY d m n) = simpleBlock (ts₀, cl₀) (guardMap (endMap P (decodeJ d m n))) := by
        unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_pos hy]
      rw [hsimple _ hop] at hab' ⊢
      have hab : x.aborted = false := by
        cases h : x.aborted
        · rfl
        · rw [guardMap_aborted _ x h, h] at hab'; cases hab'
      rw [guardMap_live _ x hab] at hab' ⊢
      -- the trace index of `n` is `J − 1`
      have hJm : decodeJ d m n ≤ m := by
        rcases gIdx_succ P n k' hk' with hkeep | ⟨-, -, -, h4, -⟩
        · exact (gIdx_some_J P n k' hkeep).resolve_left (by omega)
        · exact h4
      have hgi := gIdx_end P n hin.1 hJm hk1 hR0
      have hG := hx.2 hab _ hgi
      have hkk : decodeJ d m n - 1 ≤ k' := by
        rcases gIdx_succ P n k' hk' with hkeep | ⟨-, -, -, -, h5, -⟩
        · rw [hgi] at hkeep; cases hkeep; exact le_rfl
        · omega
      obtain ⟨-, -, hbas⟩ := hx.1 hab
      have hph := phaseOf_end P n hk1 hR0 hin.1 hin.2
      rw [hph.1] at hbas
      obtain ⟨ha, ht, hp, -, -⟩ := endMap_fields P (decodeJ d m n) x
      refine runG_lift (runG_of_fields hG (by rw [ha]; exact sweepEndActive_eq_rb x hbas.reserve)
        ht (by rw [hp]; exact Finset.subset_union_left)) hkk
    · exact hid (by unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_neg hy])
        (fun h => hy (hYs.mpr h.2.1)) hab' k' hk'
  by_cases hk2 : decodeK d m n = 2
  · by_cases hjc : decodeJ d m n ≤ m / 2
    · obtain ⟨s0, hs0, he⟩ := runOp_clear_exit P ts₀ cl₀ P.n₀ P.u (decodeJ d m n)
        (decodeY d m n) hin.1 hjc x k ω (by rw [← hk2]; exact hrun)
      rw [hk2] at hab' ⊢
      rw [he] at hab' ⊢
      have hx1 := (clr_reach P.n₀ _ P.u _ x s0 hs0).1
      have hab : x.aborted = false := by
        have : (clearingExit (d := d) (m := m) (decodeJ d m n) (decodeY d m n) s0).aborted =
            x.aborted := by
          rcases clr_exit_cases (decodeJ d m n) (decodeY d m n) s0 with h | h | h <;>
            rw [h, hx1] <;> rfl
        rw [← this]; exact hab'
      have hJm : decodeJ d m n ≤ m := by omega
      have hkk : k' = decodeJ d m n := by
        rcases gIdx_succ P n k' hk' with hkeep | ⟨h1, -⟩
        · rw [gIdx_clear P n hin.1 hJm (Or.inl hk2)] at hkeep; cases hkeep; rfl
        · omega
      subst hkk
      have hph := (boxPhase_clear P n hk2 hin.1 hJm).1
      obtain ⟨⟨⟨-, -⟩, -⟩, hXc⟩ := hcl _ _ hph
      obtain ⟨D, hpos, -, -, -⟩ := hXc hjc hab
      have hpos' : ClearRecPos (2 ^ 25) P.n₀ P.u (decodeJ d m n)
          (siteRank d m (decodeY d m n)).val x D.I.anchor := by rw [hRY]; exact hpos
      rcases clr_exit_trichotomy P.n₀ _ P.u _ x s0 hs0 with h | ⟨hne, h⟩ |
        ⟨-, hsch, hne, hf, hdn, h⟩
      · rw [h]; exact runG_of_clearRec hpos.base
      · rw [h]
        exact runG_of_clearRec (clearRecPos_fail P.n₀ _ P.u (2 ^ 25) _ x D.I.anchor hpos' s0 hs0
          hne).base
      · rw [h]
        have hDx : IsDampedEndpoint x.endpoint x.r (stageScale P.u (decodeJ d m n) m) := by
          have := D.I.physical (Fin.last D.k)
          rw [D.last, ← D.frozen] at this
          exact this
        exact runG_of_clearRec (clearRecPos_done (clearingDoneHops_proof d) P.n₀ _ P.u (2 ^ 25)
          (by norm_num) _ x D.I.anchor hpos' hDx s0 hs0 hab hsch hne hf hdn hin.1.le
          (stageScale_pos' hu _ m) (hsmall4 _ hin.1)).base
    · exact hid (by rw [hk2]; exact runOp_clear_id P ts₀ cl₀ P.n₀ P.u _ _ hjc)
        (fun h => by omega) hab' k' hk'
  have hk3 : decodeK d m n = 3 := by omega
  by_cases hjy : decodeJ d m n ≤ m ∧ decodeY d m n = site₀ d m
  · have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n)
        (decodeY d m n) = simpleBlock (ts₀, cl₀) (guardMap (stageMap P (decodeJ d m n))) := by
      unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2, if_pos hjy]
    rw [hsimple _ hop] at hab' ⊢
    have hab : x.aborted = false := by
      cases h : x.aborted
      · rfl
      · rw [guardMap_aborted _ x h, h] at hab'; cases hab'
    rw [guardMap_live _ x hab] at hab' ⊢
    have hkeep : gIdx P n = some k' := by
      rcases gIdx_succ P n k' hk' with hkeep | ⟨h1, -⟩
      · exact hkeep
      · omega
    have hG := hx.2 hab k' hkeep
    rw [stageMap_eq]
    obtain ⟨ha, ht, hp, -, -, -⟩ := stageWith_fields (resetMapA (stageScale P.u (decodeJ d m n) m))
      (resetMapA_keepsBasics _) (sweepTheta P.u m (decodeJ d m n + 1))
      (sweepScale P.u m (decodeJ d m n + 1)) (decodeJ d m n = m / 2) x
    exact runG_of_fields hG ha ht (by rw [hp]; exact Finset.subset_union_left)
  · exact hid (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2, if_neg hjy])
      (fun h => by omega) hab' k' hk'

end AndersonAC.AgentS78
