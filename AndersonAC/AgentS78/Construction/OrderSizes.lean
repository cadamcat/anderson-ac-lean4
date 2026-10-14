import AndersonAC.AgentS78.Construction.TileBlock

/-!
# WP10 construction: the order sizes `M` of the run

Only tile blocks issue order queries (tag 0 in `tileOrderIndex`). The order of trial `a` of
tile `T` in the sweep with post-sweep index `j` is a uniform order of the tile's sites
(05:338–343), so `M (tileOrderIndex j T a) = |tileSites T|`; all other indices are unused
(size 0). This is the `M` of the assembled `BlockRun` (hypothesis `hM` of `tileBlock_orders`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The order sizes of the run of a tile plan. -/
def tileOrderSize (P : TilePlan d m) (o : ℕ) : ℕ :=
  if (Nat.unpair o).1 = 0 then
    if h : (Nat.unpair (Nat.unpair (Nat.unpair o).2).1).2 <
        (P.cover (Nat.unpair (Nat.unpair (Nat.unpair o).2).1).1).cover.count then
      (tileSites (P.cover (Nat.unpair (Nat.unpair (Nat.unpair o).2).1).1)
        ⟨(Nat.unpair (Nat.unpair (Nat.unpair o).2).1).2, h⟩).card
    else 0
  else 0

theorem tileOrderSize_index (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (a : ℕ) : tileOrderSize P (tileOrderIndex j T a) = (tileSites (P.cover j) T).card := by
  have h1 : (Nat.unpair (tileOrderIndex j T a)).1 = 0 := by
    simp only [tileOrderIndex, Nat.unpair_pair]
  have h2 : Nat.unpair (Nat.unpair (Nat.unpair (tileOrderIndex j T a)).2).1 = (j, (T : ℕ)) := by
    simp only [tileOrderIndex, Nat.unpair_pair]
  unfold tileOrderSize
  rw [if_pos h1]
  generalize Nat.unpair (Nat.unpair (Nat.unpair (tileOrderIndex j T a)).2).1 = p at h2 ⊢
  subst h2
  rw [dif_pos T.isLt]

end AndersonAC.AgentS78
