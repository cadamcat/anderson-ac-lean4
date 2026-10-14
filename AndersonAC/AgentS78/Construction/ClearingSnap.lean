import AndersonAC.AgentS78.Construction.ClearingFacts
import AndersonAC.AgentS78.Construction.SnapshotComponents
import AndersonAC.AgentS78.Construction.Dichotomy

/-!
# The snapshot component is the clearing core

On a record whose components are the snapshot components of a pending set, the eligible
component anchored at `y` is the unique candidate, hence `theCore` (`theCore_snapshot`), and
a snapshot component with `N` sites lies within `N · R` of each of its sites
(`snapComp_radius`, from `component_radius`). These facts supply the inputs to
`hcrelabel` and the radius clause of `eligibleCand`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

section ClearingSnap
variable {d m : ℕ}

open Classical in
/-- A snapshot component with at most `N` sites lies within `N · R` of each of its sites. -/
theorem snapComp_radius (P : Finset (Torus d m)) (R : ℝ) (hR : 0 ≤ R) (y : Torus d m)
    (hy : y ∈ P) (N : ℕ) (hN : (snapComp P R y hy).card ≤ N) :
    ∀ v ∈ snapComp P R y hy, physicalDistance d m v y ≤ N * R := by
  intro v hv
  obtain ⟨hv', hreach⟩ := (mem_snapComp P R y hy v).mp hv
  rw [snapComp_card] at hN
  have := component_radius P R hR ⟨y, hy⟩ ⟨v, hv'⟩ N hN hreach
  unfold physicalDistance at this ⊢
  rw [SimpleGraph.dist_comm]
  exact this

/-- Real-threshold form: a component with at most `τ` sites lies within `τ · R`. -/
theorem snapComp_radius_real (P : Finset (Torus d m)) (R : ℝ) (hR : 0 ≤ R) (y : Torus d m)
    (hy : y ∈ P) (τ : ℝ) (hτ : ((snapComp P R y hy).card : ℝ) ≤ τ) :
    ∀ v ∈ snapComp P R y hy, physicalDistance d m v y ≤ τ * R := by
  intro v hv
  have h := snapComp_radius P R hR y hy (snapComp P R y hy).card le_rfl v hv
  exact h.trans (mul_le_mul_of_nonneg_right hτ hR)

/-- On snapshot records the eligible component anchored at `y` is the clearing core. -/
theorem theCore_snapshot (j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (P : Finset (Torus d m)) (R : ℝ) (hcomp : x.components = snapshotComponents P R)
    {Bc : Finset (Torus d m)} (hBc : Bc ∈ x.components)
    (hel : eligibleCand (d := d) (m := m) j u y Bc) :
    theCore (d := d) (m := m) j u y x = Bc := by
  refine theCore_eq_of_unique j u y x hBc hel (fun B hB helB => ?_)
  have hyB := (eligibleCand_parts j u y helB).1
  have hyBc := (eligibleCand_parts j u y hel).1
  rw [hcomp] at hB hBc
  obtain ⟨hy, rfl⟩ := eq_snapComp_of_mem P R B hB y hyB
  obtain ⟨hy', rfl⟩ := eq_snapComp_of_mem P R Bc hBc y hyBc
  rfl

/-- The clearing marking radius: core radius `t_j^{-ν} R_j` plus the inspection half-radius
fit in `Ch · 4^{(8+ν) j}` once `Ch ≥ u^{-ν} + 1`. -/
theorem clear_mark_radius (u : ℝ) (hu : 0 < u) (j : ℕ) (Ch : ℝ)
    (hCh : u ^ (-nu d) + 1 ≤ Ch) :
    stageScale u j m ^ (-nu d) * separationRadius j + inspectionRadius j / 2 ≤
      Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have h4j : (0 : ℝ) < 4 ^ j := by positivity
  have hlow : u / 4 ^ j ≤ stageScale u j m := by
    unfold stageScale; have : 0 ≤ u / (4 : ℝ) ^ m := by positivity
    linarith
  have hpos : 0 < u / 4 ^ j := by positivity
  have h1 : stageScale u j m ^ (-nu d) ≤ (u / 4 ^ j) ^ (-nu d) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
  have h2 : (u / 4 ^ j) ^ (-nu d) = u ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ)) := by
    rw [Real.div_rpow hu.le h4j.le, div_eq_mul_inv, ← Real.rpow_neg h4j.le, neg_neg,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hsep : separationRadius j = (4 : ℝ) ^ (8 * (j : ℝ)) := by
    unfold separationRadius; rw [← Real.rpow_natCast]; push_cast; ring_nf
  have hins : inspectionRadius j = (4 : ℝ) ^ (4 * (j : ℝ)) := by
    unfold inspectionRadius; rw [← Real.rpow_natCast]; push_cast; ring_nf
  have hsplit : (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) =
      (4 : ℝ) ^ (nu d * (j : ℝ)) * (4 : ℝ) ^ (8 * (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have hins_le : (4 : ℝ) ^ (4 * (j : ℝ)) ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (0 : ℝ) ≤ j := by positivity
      nlinarith)
  have hsepnn : 0 ≤ separationRadius j := by unfold separationRadius; positivity
  have hE : 0 ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by positivity
  have hpow : 0 ≤ u ^ (-nu d) := by positivity
  calc stageScale u j m ^ (-nu d) * separationRadius j + inspectionRadius j / 2
      ≤ (u ^ (-nu d) * (4 : ℝ) ^ (nu d * (j : ℝ))) * (4 : ℝ) ^ (8 * (j : ℝ)) +
          (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
        rw [← h2, ← hsep, hins]
        have := mul_le_mul_of_nonneg_right h1 hsepnn
        linarith
    _ = (u ^ (-nu d) + 1) * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by rw [hsplit]; ring
    _ ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := mul_le_mul_of_nonneg_right hCh hE

end ClearingSnap

end AndersonAC.AgentS78
