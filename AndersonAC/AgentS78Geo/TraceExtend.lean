import AndersonAC.S78.Definitions
import AndersonAC.S78AnchorTail.Geometry

/-!
# Extending a clearing-geometry trace by the current provisional group

07-assembly.tex:116–176 (Lemma 7.2): the current provisional group (its core `B` and the heat
pivots so far, all within `ℓ_j/2` of `B`) is one more group of the trace at index `j`.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78

variable {d m n₀ j l : ℕ} {u C : ℝ}

theorem physicalDistance_symm (x y : Torus d m) :
    physicalDistance d m x y = physicalDistance d m y x := by
  unfold physicalDistance; rw [SimpleGraph.dist_comm]

/-- The trace `T` with one more group at index `j`. -/
def extendTrace (T : ClearingGeometry d m n₀ j l u C) (core edits : Finset (Torus d m))
    (anchor : Torus d m) (hj : n₀ ≤ j) (hanchor : anchor ∈ core)
    (helig : (core.card : ℝ) ≤ stageScale u j m ^ (-nu d))
    (hrad : ∀ x ∈ core, physicalDistance d m anchor x ≤
      stageScale u j m ^ (-nu d) * separationRadius j)
    (hsep : ∀ a, T.index a = j → ∀ x ∈ T.core a, ∀ y ∈ core,
      separationRadius j < physicalDistance d m x y)
    (hsize : (edits.card : ℝ) ≤ C * (heatLimit (stageScale u j m) : ℝ))
    (hloc : ∀ x ∈ edits, ∃ y ∈ core, physicalDistance d m x y ≤ inspectionRadius j / 2) :
    ClearingGeometry d m n₀ j (l + 1) u C where
  index := Fin.lastCases j T.index
  core := Fin.lastCases core T.core
  edits := Fin.lastCases edits T.edits
  anchor := Fin.lastCases anchor T.anchor
  stages a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact ⟨hj, le_rfl⟩
    · simp only [Fin.lastCases_castSucc]; exact T.stages a
  anchorMem a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact hanchor
    · simp only [Fin.lastCases_castSucc]; exact T.anchorMem a
  eligible a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact helig
    · simp only [Fin.lastCases_castSucc]; exact T.eligible a
  coreRadius a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact hrad
    · simp only [Fin.lastCases_castSucc]; exact T.coreRadius a
  separated a b := by
    refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
    · intro h; exact absurd rfl h
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      intro _ hidx x hx y hy
      rw [physicalDistance_symm]
      exact hsep b hidx.symm y hy x hx
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      intro _ hidx x hx y hy
      rw [hidx]
      exact hsep a hidx x hx y hy
    · simp only [Fin.lastCases_castSucc]
      intro hab hidx
      exact T.separated a b (fun h => hab (by rw [h])) hidx
  groupSize a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact hsize
    · simp only [Fin.lastCases_castSucc]; exact T.groupSize a
  locations a := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [Fin.lastCases_last]; exact hloc
    · simp only [Fin.lastCases_castSucc]; exact T.locations a

theorem geometryTerminals_extendTrace (T : ClearingGeometry d m n₀ j l u C)
    (core edits : Finset (Torus d m)) (anchor : Torus d m) (hj : n₀ ≤ j) (hanchor : anchor ∈ core)
    (helig : (core.card : ℝ) ≤ stageScale u j m ^ (-nu d))
    (hrad : ∀ x ∈ core, physicalDistance d m anchor x ≤
      stageScale u j m ^ (-nu d) * separationRadius j)
    (hsep : ∀ a, T.index a = j → ∀ x ∈ T.core a, ∀ y ∈ core,
      separationRadius j < physicalDistance d m x y)
    (hsize : (edits.card : ℝ) ≤ C * (heatLimit (stageScale u j m) : ℝ))
    (hloc : ∀ x ∈ edits, ∃ y ∈ core, physicalDistance d m x y ≤ inspectionRadius j / 2) :
    geometryTerminals T ∪ edits ⊆
      geometryTerminals (extendTrace T core edits anchor hj hanchor helig hrad hsep hsize hloc) := by
  intro x hx
  simp only [geometryTerminals, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at hx ⊢
  rcases hx with ⟨a, ha⟩ | hx
  · exact ⟨a.castSucc, by simpa [extendTrace] using ha⟩
  · exact ⟨Fin.last l, by simpa [extendTrace] using hx⟩

end AndersonAC.AgentS78Geo
