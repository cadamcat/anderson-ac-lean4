import AndersonAC.AgentS78.Construction.TileTrial

/-!
# sequence facts. Generic facts on `S45.Sequence` used by the tile-phase record
invariant (TilePhase.lean):

* `SeqExtends q q'`: `q'` extends `q` (same states up to `q.length`, same pivots and scalars
  before it). Step records, accumulated records over index sets inside `range q.length`, and
  validity at `k ≤ q.length` agree (`SeqExtends.Jrecord`, …, `SeqExtends.valid`).
* Live sets of a well-formed sequence only shrink, and a port is live at `k` iff it is live at
  `0` and was no pivot before `k` (`mem_live_iff`). Hence pivots of a well-formed sequence are
  pairwise distinct (`pivot_injective`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

section Ext
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `q'` extends `q`. -/
structure SeqExtends (q q' : S45.Sequence P) : Prop where
  le : q.length ≤ q'.length
  state : ∀ k ≤ q.length, q'.state k = q.state k
  pivot : ∀ k < q.length, q'.pivot k = q.pivot k
  scalar : ∀ k < q.length, q'.scalar k = q.scalar k

theorem SeqExtends.refl (q : S45.Sequence P) : SeqExtends q q :=
  ⟨le_rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem SeqExtends.trans {q q' q'' : S45.Sequence P} (h : SeqExtends q q')
    (h' : SeqExtends q' q'') : SeqExtends q q'' :=
  ⟨h.le.trans h'.le, fun k hk => (h'.state k (hk.trans h.le)).trans (h.state k hk),
   fun k hk => (h'.pivot k (lt_of_lt_of_le hk h.le)).trans (h.pivot k hk),
   fun k hk => (h'.scalar k (lt_of_lt_of_le hk h.le)).trans (h.scalar k hk)⟩

section Records
variable {q q' : S45.Sequence P} (h : SeqExtends q q') (t : ℝ) (r : P → ℂ)
include h

theorem SeqExtends.stepJ {k : ℕ} (hk : k < q.length) : q'.stepJ t r k = q.stepJ t r k := by
  simp only [S45.Sequence.stepJ, h.pivot k hk, h.state (k + 1) hk, h.state k hk.le,
    h.scalar k hk]

theorem SeqExtends.stepL {k : ℕ} (hk : k < q.length) : q'.stepL t r k = q.stepL t r k := by
  simp only [S45.Sequence.stepL, h.pivot k hk, h.state (k + 1) hk, h.state k hk.le,
    h.scalar k hk]

theorem SeqExtends.stepLag {k : ℕ} (hk : k < q.length) :
    q'.stepLag t r k = q.stepLag t r k := by
  funext i
  simp only [S45.Sequence.stepLag, h.state (k + 1) hk, h.state k hk.le]

theorem SeqExtends.stepRow (cols : Finset P) {k : ℕ} (hk : k < q.length) :
    q'.stepRow t r cols k = q.stepRow t r cols k := by
  funext i
  simp only [S45.Sequence.stepRow, h.state (k + 1) hk, h.state k hk.le]

theorem SeqExtends.Jrecord {K : Finset ℕ} (hK : K ⊆ Finset.range q.length) :
    q'.Jrecord t r K = q.Jrecord t r K :=
  Finset.sum_congr rfl fun k hk => h.stepJ t r (Finset.mem_range.mp (hK hk))

theorem SeqExtends.Lrecord {K : Finset ℕ} (hK : K ⊆ Finset.range q.length) :
    q'.Lrecord t r K = q.Lrecord t r K :=
  Finset.sum_congr rfl fun k hk => h.stepL t r (Finset.mem_range.mp (hK hk))

theorem SeqExtends.lagRecord {K : Finset ℕ} (hK : K ⊆ Finset.range q.length) :
    q'.lagRecord t r K = q.lagRecord t r K :=
  Finset.sum_congr rfl fun k hk => h.stepLag t r (Finset.mem_range.mp (hK hk))

theorem SeqExtends.rowRecord (cols : Finset P) {K : Finset ℕ}
    (hK : K ⊆ Finset.range q.length) :
    q'.rowRecord t r cols K = q.rowRecord t r cols K :=
  Finset.sum_congr rfl fun k hk => h.stepRow t r cols (Finset.mem_range.mp (hK hk))

theorem SeqExtends.valid (D0 : S45.RMat P) {k : ℕ} (hk : k ≤ q.length) :
    q'.valid t r D0 k ↔ q.valid t r D0 k := by
  have hK : Finset.range k ⊆ Finset.range q.length := Finset.range_subset_range.mpr hk
  unfold S45.Sequence.valid
  rw [h.Jrecord t r hK, h.Lrecord t r hK, h.state k hk]

end Records

section Live
variable {q : S45.Sequence P} {t : ℝ} {r : P → ℂ}

theorem live_succ_subset (hq : q.wellFormed t r) {k : ℕ} (hk : k < q.length) :
    (q.state (k + 1)).live ⊆ (q.state k).live := by
  have h := hq.2 k hk
  rcases hp : q.pivot k with _ | x
  · simp only [hp] at h; rw [h]
  · simp only [hp] at h; rw [h.survivors]; exact Finset.erase_subset _ _

theorem pivot_live (hq : q.wellFormed t r) {k : ℕ} (hk : k < q.length) {x : P}
    (hp : q.pivot k = some x) : x ∈ (q.state k).live ∧ x ∉ (q.state (k + 1)).live := by
  have h := hq.2 k hk
  simp only [hp] at h
  rw [h.survivors]
  exact ⟨h.pivot_live, by simp⟩

/-- A port is live at `k` iff it is live at `0` and no earlier step deleted it. -/
theorem mem_live_iff (hq : q.wellFormed t r) {k : ℕ} (hk : k ≤ q.length) (x : P) :
    x ∈ (q.state k).live ↔ x ∈ (q.state 0).live ∧ ∀ l < k, q.pivot l ≠ some x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < q.length := hk
    have h := hq.2 k hk'
    rcases hp : q.pivot k with _ | y
    · simp only [hp] at h
      rw [h, ih hk'.le]
      constructor
      · rintro ⟨h0, hl⟩
        refine ⟨h0, fun l hl' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hl' | rfl
        · exact hl l hl'
        · rw [hp]; simp
      · rintro ⟨h0, hl⟩
        exact ⟨h0, fun l hl' => hl l (Nat.lt_succ_of_lt hl')⟩
    · simp only [hp] at h
      rw [h.survivors, Finset.mem_erase, ih hk'.le]
      constructor
      · rintro ⟨hne, h0, hl⟩
        refine ⟨h0, fun l hl' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hl' | rfl
        · exact hl l hl'
        · rw [hp]; simpa [eq_comm] using hne
      · rintro ⟨h0, hl⟩
        refine ⟨fun hxy => ?_, h0, fun l hl' => hl l (Nat.lt_succ_of_lt hl')⟩
        exact hl k (Nat.lt_succ_self k) (by rw [hp, hxy])

/-- Pivots of a well-formed sequence are pairwise distinct. -/
theorem pivot_injective (hq : q.wellFormed t r) {k l : ℕ} (hk : k < q.length)
    (hl : l < q.length) {x : P} (hpk : q.pivot k = some x) (hpl : q.pivot l = some x) :
    k = l := by
  by_contra hne
  have key : ∀ a b, a < b → b < q.length → q.pivot a = some x → q.pivot b = some x →
      False := by
    intro a b hab hb ha hb'
    have h1 := (pivot_live hq hb hb').1
    rw [mem_live_iff hq hb.le] at h1
    exact h1.2 a hab ha
  rcases lt_or_gt_of_ne hne with h | h
  · exact key k l h hl hpk hpl
  · exact key l k h hk hpl hpk

end Live

end Ext

/-! ## The appended step of a tile slot -/

section Extend
variable {d m : ℕ}

theorem extendSeq_extends (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (x : Port d m) (ξ : ℝ) : SeqExtends q (extendSeq q b x ξ) := by
  refine ⟨by simp [extendSeq], fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp [extendSeq, show k ≠ q.length + 1 by omega]
  · simp [extendSeq, show k ≠ q.length by omega]
  · simp [extendSeq, show k ≠ q.length by omega]

@[simp] theorem extendSeq_length (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m))
    (x : Port d m) (ξ : ℝ) : (extendSeq q b x ξ).length = q.length + 1 := rfl

@[simp] theorem extendSeq_pivot_last (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (x : Port d m) (ξ : ℝ) :
    (extendSeq q b x ξ).pivot q.length = some x := by simp [extendSeq]

@[simp] theorem extendSeq_scalar_last (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (x : Port d m) (ξ : ℝ) :
    (extendSeq q b x ξ).scalar q.length = ξ := by simp [extendSeq]

@[simp] theorem extendSeq_state_last (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (x : Port d m) (ξ : ℝ) :
    (extendSeq q b x ξ).state (q.length + 1) = b := by simp [extendSeq]

end Extend

end AndersonAC.AgentS78
