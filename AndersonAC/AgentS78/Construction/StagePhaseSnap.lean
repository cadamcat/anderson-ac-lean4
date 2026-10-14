import AndersonAC.AgentS78.Construction.StagePhaseRec

/-!
# The record clauses of the clearing phase right after the snapshot

agent-s78phase2. `clearRecPos_snapshot`: after `snapshotMap j` (components := the snapshot
components of the pending sites at radius `R_j`, Transitions.lean), the component clauses of
`ClearRecPos … j 0` hold by construction (components are pending, `R_j`-separated, of diameter at
most `|C| R_j`, and every pending site outside a component is farther than `R_j` from it). The
remaining clauses (coupled prefixes, `active = univ ∖ terminal`, `pending ⊆ active`, and a trace of
the earlier stages, all of index `< j`, with the hop structure and edits = terminal set) are
record facts that the snapshot does not touch.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf physicalDistance_symm)

variable {d m : ℕ}

/-- Two sites of distinct snapshot components are farther than `R` apart. -/
theorem snap_far (P : Finset (Torus d m)) (R : ℝ) (z w : Torus d m) (hz : z ∈ P) (hw : w ∈ P)
    (hzw : z ∉ snapComp P R w hw) : R < physicalDistance d m z w := by
  by_contra hle
  push_neg at hle
  apply hzw
  rw [mem_snapComp]
  refine ⟨hz, ?_⟩
  by_cases h : w = z
  · subst h; exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [snapshotGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun h' => h (congrArg Subtype.val h'), Or.inr hle⟩

/-- **The record clauses right after the snapshot.** -/
theorem clearRecPos_snapshot (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (j : ℕ) (x : RunRecord d m)
    (hcoupled : ∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i + n₀ = j)
    (hcompl : x.endpoint.active = Finset.univ \ x.terminal)
    (hpa : x.pending ⊆ x.endpoint.active)
    (htrace : ∃ l, ∃ T : ClearingGeometry d m n₀ j l u Ctr,
      (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
        (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
        ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
          terminalDistance (nnGraph d m) (geometryTerminals T) a b = 0) ∧
      geometryTerminals T = x.terminal ∧ ∀ a, T.index a ≠ j) :
    ClearRecPos Ctr n₀ u j 0 (snapshotMap j x) (Fin.elim0 : Fin 0 → Torus d m) := by
  have hR : (0 : ℝ) ≤ separationRadius j := by unfold separationRadius; positivity
  have hℓ : (0 : ℝ) ≤ inspectionRadius j / 2 := by unfold inspectionRadius; positivity
  have hcomp : (snapshotMap j x).components = snapshotComponents x.pending (separationRadius j) := rfl
  -- every component is the snapshot component of each of its sites
  have hsub : ∀ C ∈ (snapshotMap j x).components, C ⊆ x.pending := by
    intro C hC z hz
    rw [hcomp] at hC
    obtain ⟨hz', -⟩ := eq_snapComp_of_mem _ _ C hC z hz
    exact hz'
  have hfar : ∀ C ∈ (snapshotMap j x).components, ∀ z ∈ x.pending, z ∉ C → ∀ w ∈ C,
      separationRadius j < physicalDistance d m z w := by
    intro C hC z hz hzC w hw
    rw [hcomp] at hC
    obtain ⟨hw', hCw⟩ := eq_snapComp_of_mem _ _ C hC w hw
    exact snap_far x.pending _ z w hz hw' (hCw ▸ hzC)
  refine ⟨⟨hcoupled, hcompl, hpa, fun C hC => Or.inl (hsub C hC), ?_, ?_, ?_⟩,
    fun C hC _ => hsub C hC, ?_⟩
  · -- separated components
    intro C hC C' hC' hne z hz w hw
    refine hfar C' hC' z (hsub C hC hz) (fun hzC' => hne ?_) w hw
    rw [hcomp] at hC hC'
    obtain ⟨hz1, h1⟩ := eq_snapComp_of_mem _ _ C hC z hz
    obtain ⟨hz2, h2⟩ := eq_snapComp_of_mem _ _ C' hC' z hzC'
    rw [h1, h2]
  · -- diameter
    intro C hC y hy z hz
    rw [hcomp] at hC
    obtain ⟨hz', hCz⟩ := eq_snapComp_of_mem _ _ C hC z hz
    have := snapComp_radius_real x.pending _ hR z hz' (C.card : ℝ) (by rw [← hCz])
      y (hCz ▸ hy)
    exact this
  · -- trace
    obtain ⟨l, T, ⟨J, hJs, hJ1, hJadj, hJh⟩, hTt, hTj⟩ := htrace
    exact ⟨l, T, ⟨⟨J, hJs, hJ1, hJadj, hJh⟩, fun a ha => absurd ha (hTj a)⟩, hTt,
      fun a => a.elim0⟩
  · -- far pending sites
    intro C hC _ z hz hzC w hw
    have := hfar C hC z hz hzC w hw
    linarith

end AndersonAC.AgentS78
