import AndersonAC.AgentS78.Construction.StagePhasePkgXg
import AndersonAC.AgentS78.Construction.SweepTransport
import AndersonAC.AgentS78.Construction.ActiveCTProof
import AndersonAC.AgentS78.Construction.StagePhaseDonePhysZ

/-!
# The clearing-phase package (`ClearingPhasePackage d`)

`clearingPhasePackage_of` constructs the clearing facts of each large box
(`ClearingBoxFacts`, BoxPhases.lean) with the clearing phase indexed by the anchor
scan position, from

* `hA : ClearingDoneAnalyticStatement d` ;
* `hB : ClearingBoundR d` — the clearing first-failure bound on `ClearPhaseR` records;
and the physical identity after a DONE clearing off the exceptional set from
`clearingDonePhysZ_proof` (route R2; StagePhaseDonePhysZ.lean).

The sweep-end facts come from the unconditional `SweepEndUniformStatement`
(`sweepEndUniform_of_parts` with `sweepTransport_proof`, `sweepRowTail_proof`,
`terminalCT_proof`). Constants: broad damping `(cP/2, CP + cP/2)` (drift along the history), trace
constant `Ctr = 2^25`, scale radius `Ds = 2^9 t_j^{-8-ν}` (`CA ≥ 2^9`).
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-- **The clearing-phase package.** -/
theorem clearingPhasePackage_of (d : ℕ) (hd : 3 ≤ d) (hA : ClearingDoneAnalyticStatement d)
    (hB : ClearingBoundR d) : ClearingPhasePackage d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ Cg hCg
  have hCtr : (2 : ℝ) ≤ 2 ^ 25 := by norm_num
  obtain ⟨CA₁, cA₁, PA₁, hCA₁, hcA₁, hPA₁, hmain⟩ :=
    clearingDone_of_analytic hd (clearingDoneHops_proof d) hA cP CP hcP hCP (2 ^ 25) hCtr
  obtain ⟨CAS, hCAS, cAS, hcAS, CbS, -, hSE⟩ :=
    sweepEndUniform_of_parts (sweepTransport_proof d) (sweepRowTail_proof d) (terminalCT_proof d)
      cP CP cL CL C₀ hcP hCP hcL hCL hC₀ Cg hCg
  refine ⟨max (max CA₁ CAS) (max 512 CP), min (min cA₁ cAS) cP, PA₁,
    lt_min (lt_min hcA₁ hcAS) hcP, hPA₁, ?_⟩
  intro CA cA PA hCA hcA hcA' hPA
  have hCA1 : CA₁ ≤ CA := ((le_max_left _ _).trans (le_max_left _ _)).trans hCA
  have hCAS' : CAS ≤ CA := ((le_max_right _ _).trans (le_max_left _ _)).trans hCA
  have hCA512 : (512 : ℝ) ≤ CA := ((le_max_left _ _).trans (le_max_right _ _)).trans hCA
  have hCAP : CP ≤ CA := ((le_max_right _ _).trans (le_max_right _ _)).trans hCA
  have hcA1 : cA ≤ cA₁ := hcA'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcAS' : cA ≤ cAS := hcA'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcAP : cA ≤ cP := hcA'.trans (min_le_right _ _)
  have hPA0 : 0 ≤ PA := hPA₁.trans hPA
  obtain ⟨N₁, t₁, ht₁, hinst⟩ := hmain CA cA PA hCA1 hcA hcA1 hPA
  refine ⟨CbS, fun Cb hCb => ?_⟩
  obtain ⟨c, hc, NB, hBB⟩ := hB cP CP (2 ^ 25) CA cA PA Cb hcP hCP hCtr (by linarith) hcA hPA0
  obtain ⟨t0, ht0, hSEst⟩ := hSE Cb hCb CA hCAS' cA hcA hcAS'
  obtain ⟨Ns, hNs⟩ := stageScale_small (lt_min ht₁ (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨Nw, hNw⟩ := sweepScale_small ht0
  refine ⟨c, hc, max (max N₁ NB) (max Ns (max Nw 1)), ?_⟩
  intro n₀ m hN hm u hu E ρ P hPn hPu hSBh ts₀ cl₀ lab
  subst hPn hPu
  have hN1 : N₁ ≤ P.n₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNB : NB ≤ P.n₀ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNs' : Ns ≤ P.n₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNw' : Nw ≤ P.n₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hn1 : 1 ≤ P.n₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hnm : P.n₀ < m := by omega
  have hss : ∀ j, P.n₀ ≤ j → stageScale P.u j m < min t₁ (1 / 4) :=
    fun j hj => hNs P.n₀ m j hNs' hj hnm.le P.u hu
  have hsmall4 : ∀ j, P.n₀ < j → stageScale P.u j m ≤ 1 / 4 :=
    fun j hj => ((hss j hj.le).trans_le (min_le_right _ _)).le
  have hst : ∀ j, P.n₀ < j → stageScale P.u j m < t₁ :=
    fun j hj => (hss j hj.le).trans_le (min_le_left _ _)
  refine ⟨{ Xg := pkgXg (2 ^ 25) P
            Xc := pkgXc cP CP (2 ^ 25) P E ρ Cb CA cA PA
            hXg0 := ?_
            hXg := pkgXg_closed P ts₀ cl₀ E ρ Cb CA cA PA cP CP cP CP hnm hu hsmall4
            hXcE := fun j y h1 h2 hy => sweepEnd_clear
              (fun m n₀ u E ρ P j x => hSEst m n₀ u E ρ P j x)
              P ts₀ cl₀ E ρ j y hy hu hn1 h1 h2 (by omega) hCA512 hcA hPA0 hcP
              (hNw P.n₀ m j hNw' h1 (by omega) hnm.le P.u hu) hSBh hcAP hCAP
            hXcC := fun j y h1 h2 => clrOp_Xc hinst hCtr P ts₀ cl₀ E ρ Cb cP CP _ j y hN1 h1 h2 hu
              (hst j h1) (hsmall4 j h1)
            hXcId := fun j r h1 h2 h3 x _ hjc => absurd hjc (by omega)
            hDone := fun j y h1 h2 x k ω hω hTV _ hx hab hrun hne hf hdn =>
              clrOp_doneZ hinst (clearingDonePhysZ_proof d) hCtr P E ρ Cb cP CP j y hN1 h1 h2 hu
                (hst j h1) (hsmall4 j h1) x k ω hω hTV hx hab hrun hne hf hdn
            hbound := fun j y h1 h2 x hx => ?_ }⟩
  · -- the initial record
    intro _ k hk
    have hg : gIdx P 0 = some P.n₀ := by
      unfold gIdx; rw [if_pos (by rw [decodeJ_zero]; exact Nat.zero_le _)]
    rw [hg] at hk; cases hk
    refine ⟨fun i => Or.inl (Finset.mem_univ i), by
      show (∅ : Finset (Torus d m)) ⊆ _; exact Finset.empty_subset _,
      0, emptyGeometry P.n₀ P.n₀ P.u (2 ^ 25), ?_, fun a => a.elim0⟩
    rw [geometryTerminals_empty]; rfl
  · -- the clearing bound
    have hR := hx.2 h2
    refine hBB m P.n₀ P.u E ρ (tileOrderSize P) j y x hNB hm hu h1 h2 hR (fun hab => ?_)
      (fun hab => ?_)
    · obtain ⟨D, hpos, -⟩ := hR hab
      rw [Finset.disjoint_left]
      intro i hi hit
      have := hpos.base.activeCompl ▸ hi
      exact (Finset.mem_sdiff.mp this).2 hit
    · obtain ⟨D, hpos, -⟩ := hR hab
      intro w hw
      have hne : theCore (d := d) (m := m) j P.u y x ≠ ∅ := Finset.ne_empty_of_mem hw
      obtain ⟨B, hBc, hel, hBeq⟩ := theCore_spec j P.u y x hne
      rw [hBeq] at hw
      exact hpos.base.pendingActive (hpos.untouched B hBc (core_ranks hel) hw)

end AndersonAC.AgentS78
