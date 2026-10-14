import AndersonAC.AgentS78.Construction.ClearingBlock

/-! Type audit for the clearing-attempt block (muse-s78clear).
Exact-shape checks against the `BlockRun` consumer fields
(`RunOpsData`: `clr j y`, `clrPat j y`; `BlockRun`: measurability,
orders/aux with `orderSet = auxSet = ∅`, pattern, `fail_local`). -/

open AndersonAC.AgentS78
open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query sourcesLaw)

noncomputable section
set_option autoImplicit false

/-- The block has the `BlockRun`-ready type (for fixed `n₀ u`,
`clr j y := clearingBlock n₀ j u y`). -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Block (Torus d m) (RunRecord d m) (RunRecord d m × ClearScratch d m) :=
  clearingBlock (d := d) (m := m) n₀ j u x

/-- Measurability has the `Block.IsMeasurable` shape (`hcmeas`). -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).IsMeasurable :=
  clearingBlock_measurable (d := d) (m := m) n₀ j u x

/-- Order discipline matches `BlockRun.orders` for `orderSet = ∅` (`hcorders`). -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) (M : ℕ → ℕ) :
    ∀ r k ω o, (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) = false →
    (clearingBlock (d := d) (m := m) n₀ j u x).next
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) =
        Query.nextOrder o →
    o ∈ (∅ : Set ℕ) ∧
    ((List.range k).filter fun k' =>
      (clearingBlock (d := d) (m := m) n₀ j u x).halted
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) = false ∧
      (clearingBlock (d := d) (m := m) n₀ j u x).next
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) =
        Query.nextOrder o).length < M o :=
  clearingBlock_orders (d := d) (m := m) n₀ j u x M ∅

/-- Aux discipline matches `BlockRun.aux` for `auxSet = ∅` (`hcaux`). -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) (M : ℕ → ℕ) :
    ∀ r k ω a, (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) = false →
    (clearingBlock (d := d) (m := m) n₀ j u x).next
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) =
        Query.auxiliary a →
    a ∈ (∅ : Set ℕ) ∧ ∀ k' < k,
      (clearingBlock (d := d) (m := m) n₀ j u x).halted
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) =
        false →
      (clearingBlock (d := d) (m := m) n₀ j u x).next
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) ≠
        Query.auxiliary a :=
  clearingBlock_aux (d := d) (m := m) n₀ j u x M ∅

/-- Pattern measurability (`hcpatm`): for fixed `n₀ j u x`,
`clrPat j y = clearingPattern n₀ j u y` is measurable in the record. -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearingPattern (d := d) (m := m) n₀ j u x) :=
  clearingPattern_measurable (d := d) (m := m) n₀ j u x

/-- `fail_local` (`hclocal`). -/
example {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (M : ℕ → ℕ) (r : RunRecord d m) :
    DependsOnly (Torus d m) (M := M)
      (clearingPattern (d := d) (m := m) n₀ j u x r)
      (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) r) :=
  clearingBlock_fail_local (d := d) (m := m) n₀ j u x M r

#print axioms AndersonAC.AgentS78.clearingBlock
#print axioms AndersonAC.AgentS78.clearingBlock_orders
#print axioms AndersonAC.AgentS78.clearingBlock_aux
#print axioms AndersonAC.AgentS78.clearingBlock_measurable
#print axioms AndersonAC.AgentS78.clearingPattern_measurable
#print axioms AndersonAC.AgentS78.clearingBlock_fail_local
