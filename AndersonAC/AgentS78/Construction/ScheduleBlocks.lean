import AndersonAC.AgentS78.Construction.Schedule
import AndersonAC.AgentS78.Construction.Blocks

/-!
# the block sequence of the schedule

Block index `n` is the operation `opIndex d m j k y` (Schedule.lean) with `j = decodeJ n`,
`k = decodeK n < 4`, `y = decodeY n`; `opIndex_decode` and `decode_opIndex` make this a
bijection between `ℕ` and the triples with `k < 4`. `scheduleBlocks op` is the block sequence
of an operation family `op j k y`; per-index properties are proved per operation
(`forall_index`), and index sets indexed by operations are pairwise disjoint as soon as they
are for distinct operations (`pairwise_disjoint_of_ops`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- Stage of block index `n`. -/
def decodeJ (d m n : ℕ) : ℕ := n / (4 * siteCount d m)

/-- Operation kind of block index `n`. -/
def decodeK (d m n : ℕ) : ℕ := (n / siteCount d m) % 4

/-- Site of block index `n`. -/
def decodeY (d m n : ℕ) : Torus d m :=
  (siteRank d m).symm ⟨n % siteCount d m, Nat.mod_lt _ (siteCount_pos d m)⟩

theorem decodeK_lt (n : ℕ) : decodeK d m n < 4 := Nat.mod_lt _ (by norm_num)

theorem opIndex_decode (n : ℕ) : opIndex d m (decodeJ d m n) (decodeK d m n) (decodeY d m n) = n := by
  unfold opIndex decodeJ decodeK decodeY
  rw [Equiv.apply_symm_apply]
  simp only
  have h1 : n / (4 * siteCount d m) = n / siteCount d m / 4 := by
    rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
  rw [h1]
  have h2 := Nat.div_add_mod (n / siteCount d m) 4
  have h3 := Nat.div_add_mod n (siteCount d m)
  calc (4 * (n / siteCount d m / 4) + n / siteCount d m % 4) * siteCount d m +
        n % siteCount d m = (n / siteCount d m) * siteCount d m + n % siteCount d m := by
          rw [h2]
    _ = n := by rw [Nat.mul_comm]; exact h3

theorem decode_opIndex (j k : ℕ) (y : Torus d m) (hk : k < 4) :
    decodeJ d m (opIndex d m j k y) = j ∧ decodeK d m (opIndex d m j k y) = k ∧
      decodeY d m (opIndex d m j k y) = y := by
  have hdiv := opIndex_div d m j k y
  have hmod := opIndex_mod d m j k y
  refine ⟨?_, ?_, ?_⟩
  · unfold decodeJ
    rw [Nat.mul_comm 4, ← Nat.div_div_eq_div_mul, hdiv]; omega
  · unfold decodeK; rw [hdiv]; omega
  · unfold decodeY
    apply (siteRank d m).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext hmod

/-- Per-index properties from per-operation properties. -/
theorem forall_index (P : ℕ → Prop)
    (h : ∀ j k (y : Torus d m), k < 4 → P (opIndex d m j k y)) : ∀ n, P n := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  exact h _ _ _ (decodeK_lt n)

/-- The block sequence of an operation family. -/
def scheduleBlocks {ι Rec St : Type} [Fintype ι] [DecidableEq ι]
    (op : ℕ → ℕ → Torus d m → Block ι Rec St) (n : ℕ) : Block ι Rec St :=
  op (decodeJ d m n) (decodeK d m n) (decodeY d m n)

theorem scheduleBlocks_opIndex {ι Rec St : Type} [Fintype ι] [DecidableEq ι]
    (op : ℕ → ℕ → Torus d m → Block ι Rec St) (j k : ℕ) (y : Torus d m) (hk : k < 4) :
    scheduleBlocks op (opIndex d m j k y) = op j k y := by
  obtain ⟨h1, h2, h3⟩ := decode_opIndex j k y hk
  unfold scheduleBlocks
  rw [h1, h2, h3]

/-- An index family given by operations. -/
def scheduleSets {α : Type} (S : ℕ → ℕ → Torus d m → Set α) (n : ℕ) : Set α :=
  S (decodeJ d m n) (decodeK d m n) (decodeY d m n)

/-- Index sets of distinct operations are disjoint, hence those of distinct blocks. -/
theorem pairwise_disjoint_of_ops {α : Type} (S : ℕ → ℕ → Torus d m → Set α)
    (h : ∀ j k y j' k' y', k < 4 → k' < 4 → (j, k, y) ≠ (j', k', y') →
      Disjoint (S j k y) (S j' k' y')) :
    Pairwise fun n n' => Disjoint (scheduleSets (d := d) (m := m) S n) (scheduleSets S n') := by
  intro n n' hne
  apply h _ _ _ _ _ _ (decodeK_lt n) (decodeK_lt n')
  intro heq
  apply hne
  rw [← opIndex_decode (d := d) (m := m) n, ← opIndex_decode (d := d) (m := m) n']
  simp only [Prod.mk.injEq] at heq
  rw [heq.1, heq.2.1, heq.2.2]

/-- The label of a block is the label of its operation. -/
theorem opLabel_decode (n : ℕ) : opLabel d m n =
    ⟨decodeJ d m n, if decodeK d m n = 2 then .clearing else .tile, decodeY d m n⟩ := rfl

end AndersonAC.AgentS78
