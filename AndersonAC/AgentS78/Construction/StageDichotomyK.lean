import AndersonAC.AgentS78.Construction.StageDichotomy

/-!
# the stage dichotomy with the schedule's eligibility threshold

The schedule attempts the snapshot components with `|B| ≤ t_j^{-ν}`, `t_j = stageScale u j m`
(07-assembly.tex:18–34), while the dichotomy of `BlockRun` counts large components against
`stageScale 1 j m ^ (-ν) ≤ t_j^{-ν}`. `stage_dichotomy_K` takes any threshold `K` with
`⌊stageScale 1 j m ^ (-ν)⌋ ≤ K`: components of size `≤ K` are attempted, larger ones are left
alone, and the large case of the dichotomy still holds.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

open Classical in
/-- `snapshot_rule` with an arbitrary eligibility threshold `K` (the schedule attempts the
components with `|B| ≤ t_j^{-ν}`, `t_j = stageScale u j m`). -/
theorem snapshot_rule_K (K : ℕ) (r : ℕ → RunRecord d m) (a b j : ℕ) (hab : a ≤ b)
    (Rel : ℕ → RunRecord d m → RunRecord d m → Prop) (label : ℕ → BirthLabel (Torus d m))
    (hrel : ∀ n, a ≤ n → n < b → Rel n (r n) (r (n + 1)))
    (hscale : ∀ n, a ≤ n → n < b → (label n).scale = j)
    (hmark : ∀ n x x', Rel n x x' → ∀ y ∈ x'.pending,
      (y ∈ x.pending ∧ x'.latest y = x.latest y) ∨ x'.latest y = label n)
    (hattempt : ∀ y (hy : y ∈ (r a).pending),
      (Finset.univ.filter ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable
        ⟨y, hy⟩)).card ≤ K →
      ∃ n, a ≤ n ∧ n < b ∧ ∀ x x', Rel n x x' → y ∈ x'.pending → x'.latest y = label n)
    (hlocal : ∀ y (hy : y ∈ (r a).pending),
      K < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨y, hy⟩)).card →
      ∀ n, a ≤ n → n < b → ∀ x x', Rel n x x' → y ∈ x.pending →
        y ∈ x'.pending ∧ x'.latest y = x.latest y)
    (x : Torus d m) (hx : x ∈ (r b).pending) :
    ((r b).latest x).scale = j ∨ ∃ hxP : x ∈ (r a).pending,
      K < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨x, hxP⟩)).card ∧
      ∀ y (hy : y ∈ (r a).pending),
        (snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨x, hxP⟩ ⟨y, hy⟩ →
        y ∈ (r b).pending := by
  set G := snapshotGraph d m (r a).pending (separationRadius j)
  rcases chain_untouched r a Rel label hmark b hab hrel x hx with hun | ⟨n, h1, h2, h3⟩
  · have hxa := (hun a le_rfl hab).1
    by_cases hbig : K < (Finset.univ.filter (G.Reachable ⟨x, hxa⟩)).card
    · right
      refine ⟨hxa, hbig, fun y hy hreach => ?_⟩
      -- y lies in the same (huge) component, hence untouched through the stage
      have hcomp : (Finset.univ.filter (G.Reachable ⟨y, hy⟩)) =
          (Finset.univ.filter (G.Reachable ⟨x, hxa⟩)) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => hreach.trans h, fun h => hreach.symm.trans h⟩
      have hbigy : K < (Finset.univ.filter (G.Reachable ⟨y, hy⟩)).card := by
        rw [hcomp]; exact hbig
      have key : ∀ n, a ≤ n → n ≤ b → y ∈ (r n).pending := by
        intro n h1 h2
        induction n, h1 using Nat.le_induction with
        | base => exact hy
        | succ n hn ih =>
          exact (hlocal y hy hbigy n hn (by omega) _ _ (hrel n hn (by omega)) (ih (by omega))).1
      exact key b hab le_rfl
    · left
      obtain ⟨n, h1, h2, hatt⟩ := hattempt x hxa (not_lt.mp hbig)
      have hn1 := hun (n + 1) (by omega) (by omega)
      have hlab := hatt _ _ (hrel n h1 h2) hn1.1
      rw [(hun b hab le_rfl).2, ← hn1.2, hlab]
      exact hscale n h1 h2
  · left; rw [h3]; exact hscale n h1 h2

open Classical in
/-- **Stage dichotomy with threshold `K`.** -/
theorem stage_dichotomy_K (hd : 0 < d) (Ch : ℝ) (hCh : 1 ≤ Ch) (K : ℕ)
    (r : ℕ → RunRecord d m) (a b j : ℕ) (hab : a ≤ b)
    (hK : ⌊stageScale 1 j m ^ (-nu d)⌋₊ ≤ K)
    (Rel : ℕ → RunRecord d m → RunRecord d m → Prop) (label : ℕ → BirthLabel (Torus d m))
    (hrel : ∀ n, a ≤ n → n < b → Rel n (r n) (r (n + 1)))
    (hscale : ∀ n, a ≤ n → n < b → (label n).scale = j)
    (hmark : ∀ n x x', Rel n x x' → ∀ y ∈ x'.pending,
      (y ∈ x.pending ∧ x'.latest y = x.latest y) ∨ x'.latest y = label n)
    (hattempt : ∀ y (hy : y ∈ (r a).pending),
      (Finset.univ.filter ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable
        ⟨y, hy⟩)).card ≤ K →
      ∃ n, a ≤ n ∧ n < b ∧ ∀ x x', Rel n x x' → y ∈ x'.pending → x'.latest y = label n)
    (hlocal : ∀ y (hy : y ∈ (r a).pending),
      K < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨y, hy⟩)).card →
      ∀ n, a ≤ n → n < b → ∀ x x', Rel n x x' → y ∈ x.pending →
        y ∈ x'.pending ∧ x'.latest y = x.latest y)
    (x : Torus d m) (hx : x ∈ (r b).pending) :
    ((r b).latest x).scale = j ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, y ∈ (r b).pending) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) := by
  apply dichotomy_of_snapshot hd Ch hCh (r a).pending (r b).pending ((r b).latest x) x
  rcases snapshot_rule_K K r a b j hab Rel label hrel hscale hmark hattempt hlocal x hx with
    h | ⟨hxP, hbig, hall⟩
  · exact Or.inl h
  · exact Or.inr ⟨hxP, lt_of_le_of_lt hK hbig, hall⟩

theorem stageScale_eq_mul (u : ℝ) (j m : ℕ) : stageScale u j m = u * stageScale 1 j m := by
  unfold stageScale; ring

/-- The schedule's threshold dominates the dichotomy's. -/
theorem floor_threshold_le {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) (j m : ℕ) :
    ⌊stageScale 1 j m ^ (-nu d)⌋₊ ≤ ⌊stageScale u j m ^ (-nu d)⌋₊ := by
  apply Nat.floor_le_floor
  have hs : 0 < stageScale 1 j m := by unfold stageScale; positivity
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  rw [stageScale_eq_mul u j m, Real.mul_rpow hu.1.le hs.le]
  have h1 : 1 ≤ u ^ (-nu d) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu.2 (by linarith)
  have h2 : 0 ≤ stageScale 1 j m ^ (-nu d) := Real.rpow_nonneg hs.le _
  nlinarith

end AndersonAC.AgentS78
