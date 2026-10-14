import AndersonAC.AgentS78.Construction.Dichotomy
import AndersonAC.AgentS78.Construction.Record

/-!
# the snapshot rule over the clearings of one stage

07-assembly.tex:18–34, 08-history.tex:119–125. Let `r a, …, r b` be the committed records
between the snapshot of stage `j` and the end of the stage, consecutive ones related by
the blocks of the stage. If every block keeps or relabels (with a stage-`j` label) pending
sites, every site of an eligible snapshot component is relabelled by that component's
attempt if it is still pending afterwards, and no block touches the sites of huge
components, then the hypothesis `hrule` of `dichotomy_of_snapshot` holds at the end of the
stage (`snapshot_rule`). Pure record bookkeeping; the three per-block properties are the
clearing block's (and reset/snapshot blocks') disciplines.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- Along a chain of records, a pending site at the end was either untouched throughout or
relabelled by some step. -/
theorem chain_untouched (r : ℕ → RunRecord d m) (a : ℕ)
    (Rel : ℕ → RunRecord d m → RunRecord d m → Prop) (label : ℕ → BirthLabel (Torus d m))
    (hmark : ∀ n x x', Rel n x x' → ∀ y ∈ x'.pending,
      (y ∈ x.pending ∧ x'.latest y = x.latest y) ∨ x'.latest y = label n) :
    ∀ b, a ≤ b → (∀ n, a ≤ n → n < b → Rel n (r n) (r (n + 1))) →
      ∀ y ∈ (r b).pending,
        (∀ n, a ≤ n → n ≤ b → y ∈ (r n).pending ∧ (r n).latest y = (r a).latest y) ∨
        ∃ n, a ≤ n ∧ n < b ∧ (r b).latest y = label n := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ y hy
    left; intro n h1 h2
    have : n = a := le_antisymm h2 h1
    subst this; exact ⟨hy, rfl⟩
  | succ b hab ih =>
    intro hrel y hy
    rcases hmark b _ _ (hrel b hab (Nat.lt_succ_self b)) y hy with ⟨hy', hl⟩ | hl
    · rcases ih (fun n h1 h2 => hrel n h1 (Nat.lt_succ_of_lt h2)) y hy' with h | ⟨n, h1, h2, h3⟩
      · left; intro n h1 h2
        rcases Nat.lt_or_ge n (b + 1) with h' | h'
        · exact h n h1 (by omega)
        · have : n = b + 1 := by omega
          subst this
          exact ⟨hy, hl.trans (h b hab le_rfl).2⟩
      · right; exact ⟨n, h1, Nat.lt_succ_of_lt h2, hl.trans h3⟩
    · right; exact ⟨b, hab, Nat.lt_succ_self b, hl⟩

open Classical in
/-- **The snapshot rule of one clearing stage**, in the form `hrule` of
`dichotomy_of_snapshot`. -/
theorem snapshot_rule (r : ℕ → RunRecord d m) (a b j : ℕ) (hab : a ≤ b)
    (Rel : ℕ → RunRecord d m → RunRecord d m → Prop) (label : ℕ → BirthLabel (Torus d m))
    (hrel : ∀ n, a ≤ n → n < b → Rel n (r n) (r (n + 1)))
    (hscale : ∀ n, a ≤ n → n < b → (label n).scale = j)
    (hmark : ∀ n x x', Rel n x x' → ∀ y ∈ x'.pending,
      (y ∈ x.pending ∧ x'.latest y = x.latest y) ∨ x'.latest y = label n)
    (hattempt : ∀ y (hy : y ∈ (r a).pending),
      (Finset.univ.filter ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable
        ⟨y, hy⟩)).card ≤ ⌊stageScale 1 j m ^ (-nu d)⌋₊ →
      ∃ n, a ≤ n ∧ n < b ∧ ∀ x x', Rel n x x' → y ∈ x'.pending → x'.latest y = label n)
    (hlocal : ∀ y (hy : y ∈ (r a).pending),
      ⌊stageScale 1 j m ^ (-nu d)⌋₊ < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨y, hy⟩)).card →
      ∀ n, a ≤ n → n < b → ∀ x x', Rel n x x' → y ∈ x.pending →
        y ∈ x'.pending ∧ x'.latest y = x.latest y)
    (x : Torus d m) (hx : x ∈ (r b).pending) :
    ((r b).latest x).scale = j ∨ ∃ hxP : x ∈ (r a).pending,
      ⌊stageScale 1 j m ^ (-nu d)⌋₊ < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨x, hxP⟩)).card ∧
      ∀ y (hy : y ∈ (r a).pending),
        (snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨x, hxP⟩ ⟨y, hy⟩ →
        y ∈ (r b).pending := by
  set G := snapshotGraph d m (r a).pending (separationRadius j)
  set K := ⌊stageScale 1 j m ^ (-nu d)⌋₊
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

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

open Classical in
/-- **Stage dichotomy** for the records of one clearing stage: the `dichotomy` field of
`PendingHistory`/`BlockRun` at the end of the stage. -/
theorem stage_dichotomy {d m : ℕ} (hd : 0 < d) (Ch : ℝ) (hCh : 1 ≤ Ch)
    (r : ℕ → RunRecord d m) (a b j : ℕ) (hab : a ≤ b)
    (Rel : ℕ → RunRecord d m → RunRecord d m → Prop) (label : ℕ → BirthLabel (Torus d m))
    (hrel : ∀ n, a ≤ n → n < b → Rel n (r n) (r (n + 1)))
    (hscale : ∀ n, a ≤ n → n < b → (label n).scale = j)
    (hmark : ∀ n x x', Rel n x x' → ∀ y ∈ x'.pending,
      (y ∈ x.pending ∧ x'.latest y = x.latest y) ∨ x'.latest y = label n)
    (hattempt : ∀ y (hy : y ∈ (r a).pending),
      (Finset.univ.filter ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable
        ⟨y, hy⟩)).card ≤ ⌊stageScale 1 j m ^ (-nu d)⌋₊ →
      ∃ n, a ≤ n ∧ n < b ∧ ∀ x x', Rel n x x' → y ∈ x'.pending → x'.latest y = label n)
    (hlocal : ∀ y (hy : y ∈ (r a).pending),
      ⌊stageScale 1 j m ^ (-nu d)⌋₊ < (Finset.univ.filter
        ((snapshotGraph d m (r a).pending (separationRadius j)).Reachable ⟨y, hy⟩)).card →
      ∀ n, a ≤ n → n < b → ∀ x x', Rel n x x' → y ∈ x.pending →
        y ∈ x'.pending ∧ x'.latest y = x.latest y)
    (x : Torus d m) (hx : x ∈ (r b).pending) :
    ((r b).latest x).scale = j ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, y ∈ (r b).pending) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) :=
  dichotomy_of_snapshot hd Ch hCh (r a).pending (r b).pending ((r b).latest x) x
    (snapshot_rule r a b j hab Rel label hrel hscale hmark hattempt hlocal x hx)

end AndersonAC.AgentS78
