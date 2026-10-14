import AndersonAC.AgentS78.Construction.HugePiece
import AndersonAC.S78.Statements

/-!
# WP10 construction, C5c: the clearing-stage dichotomy from the snapshot rule

08-history.tex:119–125 and 07-assembly.tex:18–34. After the clearings of stage `j`, a
pending site either carries a label of stage `j`, or it was pending at the snapshot and its
snapshot component (edges at physical distance ≤ R_j = 4^{8j}) is huge (more than
⌊t_j^{-ν}⌋ sites) and was left untouched, all of its sites still pending. From this rule,
`dichotomy_of_snapshot` gives exactly the `dichotomy` field of `PendingHistory`/`SlotRun`
(with any constant `Ch ≥ 1`).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Physical distance along a walk of the snapshot graph. -/
theorem physicalDistance_le_walk {d m : ℕ} (P : Finset (Torus d m)) (R : ℝ)
    {a b : P} (w : (snapshotGraph d m P R).Walk a b) :
    physicalDistance d m a.val b.val ≤ w.length * R := by
  induction w with
  | nil => simp [physicalDistance, SimpleGraph.dist_self]
  | @cons a b c h p ih =>
    have hab : physicalDistance d m a.val b.val ≤ R := by
      rcases (SimpleGraph.fromRel_adj _ _ _).mp h with ⟨-, h1 | h1⟩
      · exact h1
      · unfold physicalDistance at h1 ⊢; rw [SimpleGraph.dist_comm]; exact h1
    have htri : physicalDistance d m a.val c.val ≤
        physicalDistance d m a.val b.val + physicalDistance d m b.val c.val := by
      unfold physicalDistance
      exact_mod_cast (AndersonAC.SolS78.nnGraph_connected_proof (d := d) (m := m)).dist_triangle
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    linarith

theorem snapshot_radius_bound (d j m : ℕ) (hd : 0 < d) :
    stageScale 1 j m ^ (-nu d) * separationRadius j ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have h4j : (0 : ℝ) < (4 : ℝ) ^ (-(j : ℝ)) := by positivity
  have ht : (4 : ℝ) ^ (-(j : ℝ)) ≤ stageScale 1 j m := by
    unfold stageScale
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have : (0 : ℝ) ≤ 1 / (4 : ℝ) ^ m := by positivity
    simp only [one_div] at this ⊢
    linarith
  have h1 : stageScale 1 j m ^ (-nu d) ≤ ((4 : ℝ) ^ (-(j : ℝ))) ^ (-nu d) :=
    Real.rpow_le_rpow_of_nonpos h4j ht (by linarith)
  have h2 : ((4 : ℝ) ^ (-(j : ℝ))) ^ (-nu d) = (4 : ℝ) ^ (nu d * j) := by
    rw [← Real.rpow_mul (by norm_num)]; ring_nf
  have h3 : separationRadius j = (4 : ℝ) ^ (8 * (j : ℝ)) := by
    unfold separationRadius; rw [← Real.rpow_natCast]; push_cast; ring_nf
  calc stageScale 1 j m ^ (-nu d) * separationRadius j
      ≤ (4 : ℝ) ^ (nu d * j) * (4 : ℝ) ^ (8 * (j : ℝ)) := by
        rw [h3, ← h2]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf

open Classical in
/-- **Dichotomy from the snapshot rule** (08-history.tex:119–125). -/
theorem dichotomy_of_snapshot {d m j : ℕ} (hd : 0 < d) (Ch : ℝ) (hCh : 1 ≤ Ch)
    (P P' : Finset (Torus d m)) (lat : BirthLabel (Torus d m)) (x : Torus d m)
    (hrule : lat.scale = j ∨ ∃ hxP : x ∈ P,
      ⌊stageScale 1 j m ^ (-nu d)⌋₊ < (Finset.univ.filter
        ((snapshotGraph d m P (separationRadius j)).Reachable ⟨x, hxP⟩)).card ∧
      ∀ y (hy : y ∈ P), (snapshotGraph d m P (separationRadius j)).Reachable ⟨x, hxP⟩ ⟨y, hy⟩ →
        y ∈ P') :
    lat.scale = j ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, y ∈ P') ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) := by
  rcases hrule with h | ⟨hxP, hbig, hkeep⟩
  · exact Or.inl h
  right
  obtain ⟨S', hxS', hcard, hwalk⟩ :=
    exists_bounded_piece (snapshotGraph d m P (separationRadius j)) ⟨x, hxP⟩ _ hbig
  refine ⟨S'.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_map.mpr ⟨⟨x, hxP⟩, hxS', rfl⟩
  · rw [Finset.card_map, hcard]
    have := Nat.lt_floor_add_one (stageScale 1 j m ^ (-nu d))
    push_cast; exact this
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨w, -⟩ := hwalk y' hy'
    exact hkeep y'.val y'.property ⟨w⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨w, hw⟩ := hwalk y' hy'
    have hR : (0 : ℝ) ≤ separationRadius j := by unfold separationRadius; positivity
    have hdist := physicalDistance_le_walk P (separationRadius j) w
    have hKt : ((⌊stageScale 1 j m ^ (-nu d)⌋₊ : ℕ) : ℝ) ≤ stageScale 1 j m ^ (-nu d) :=
      Nat.floor_le (by unfold stageScale; positivity)
    have hlen : (w.length : ℝ) ≤ ((⌊stageScale 1 j m ^ (-nu d)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hw
    have hrad := snapshot_radius_bound d j m hd
    have hpos : (0 : ℝ) ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by positivity
    calc physicalDistance d m x y'.val ≤ w.length * separationRadius j := hdist
      _ ≤ stageScale 1 j m ^ (-nu d) * separationRadius j :=
          mul_le_mul_of_nonneg_right (hlen.trans hKt) hR
      _ ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := hrad
      _ ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := le_mul_of_one_le_left hpos hCh

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Every site of a snapshot component with at most `N` sites lies within `N R` of each
other site of it (the mark radius of a failed clearing, 08-history.tex:109–117). -/
theorem component_radius {d m : ℕ} (P : Finset (Torus d m)) (R : ℝ) (hR : 0 ≤ R)
    (a b : P) [DecidablePred ((snapshotGraph d m P R).Reachable a)] (N : ℕ)
    (hN : (Finset.univ.filter ((snapshotGraph d m P R).Reachable a)).card ≤ N)
    (hab : (snapshotGraph d m P R).Reachable a b) :
    physicalDistance d m a.val b.val ≤ N * R := by
  classical
  obtain ⟨w⟩ := hab
  let p := w.toPath
  have hsupp : p.val.support.toFinset ⊆ Finset.univ.filter ((snapshotGraph d m P R).Reachable a) := by
    intro v hv
    rw [List.mem_toFinset] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.val.takeUntil v hv⟩⟩
  have hlen : p.val.length + 1 ≤ N := by
    have h1 := Finset.card_le_card hsupp
    rw [List.toFinset_card_of_nodup p.property.support_nodup, SimpleGraph.Walk.length_support] at h1
    omega
  have hd := physicalDistance_le_walk P R p.val
  have : (p.val.length : ℝ) ≤ N := by exact_mod_cast (by omega : p.val.length ≤ N)
  calc physicalDistance d m a.val b.val ≤ p.val.length * R := hd
    _ ≤ N * R := mul_le_mul_of_nonneg_right this hR

end AndersonAC.AgentS78
