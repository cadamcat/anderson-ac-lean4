import AndersonAC.AgentS78.Construction.QueryRun

/-!
# WP10 random construction, C1: the deterministic chronological slot schedule

08-history.tex:52–63. Every possible birth label gets one bookkeeping slot, ordered by
increasing scale, then tile slots before clearing slots, then site order of the anchor
(the designated site of a tile, or the least site of a snapshot component). Unscheduled or
skipped labels keep their slot with an empty trial. The late tile slots are the tile labels
of the one-digit sweeps into the stages ⌊m/2⌋ < j ≤ m and of the final residual sweep, which
is scheduled as stage `m+1` (04-sweep.tex:36–41, 08-history.tex:340–353).
-/

open scoped BigOperators
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Number of torus sites. -/
abbrev siteCount (d m : ℕ) : ℕ := Fintype.card (Torus d m)

/-- The fixed total order of torus sites. -/
def siteRank (d m : ℕ) : Torus d m ≃ Fin (siteCount d m) := Fintype.equivFin _

/-- Operation kinds within a stage: 0 tile trial, 1 snapshot, 2 clearing attempt,
3 reset / cutoff. Birth labels use kinds 0 and 2. -/
def kindIndex : BirthType → ℕ
  | .tile => 0
  | .clearing => 2

theorem kindIndex_lt (k : BirthType) : kindIndex k < 4 := by cases k <;> simp [kindIndex]

theorem kindIndex_injective : Function.Injective kindIndex := by
  intro a b h; cases a <;> cases b <;> simp_all [kindIndex]

/-- The chronological index of operation `(j, kind, x)` of the run (block index). -/
def opIndex (d m j k : ℕ) (x : Torus d m) : ℕ :=
  (4 * j + k) * siteCount d m + (siteRank d m x).val

/-- The chronological slot of a birth label. -/
def slotIndex {d m : ℕ} (a : BirthLabel (Torus d m)) : ℕ :=
  (4 * a.scale + kindIndex a.kind) * siteCount d m + (siteRank d m a.anchor).val

theorem slotIndex_eq_opIndex {d m : ℕ} (a : BirthLabel (Torus d m)) :
    slotIndex a = opIndex d m a.scale (kindIndex a.kind) a.anchor := rfl

/-- The scale of a slot. -/
def slotScaleOf (d m n : ℕ) : ℕ := n / (4 * siteCount d m)

theorem siteCount_pos (d m : ℕ) : 0 < siteCount d m := Fintype.card_pos

theorem slotIndex_div {d m : ℕ} (a : BirthLabel (Torus d m)) :
    slotIndex a / siteCount d m = 4 * a.scale + kindIndex a.kind := by
  unfold slotIndex
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (siteCount_pos d m),
    Nat.div_eq_of_lt (siteRank d m a.anchor).isLt, zero_add]

theorem slotIndex_mod {d m : ℕ} (a : BirthLabel (Torus d m)) :
    slotIndex a % siteCount d m = (siteRank d m a.anchor).val := by
  unfold slotIndex
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (siteRank d m a.anchor).isLt]

theorem slotScaleOf_slotIndex {d m : ℕ} (a : BirthLabel (Torus d m)) :
    slotScaleOf d m (slotIndex a) = a.scale := by
  unfold slotScaleOf
  rw [Nat.mul_comm 4, ← Nat.div_div_eq_div_mul, slotIndex_div]
  have := kindIndex_lt a.kind
  omega

theorem slotIndex_injective (d m : ℕ) :
    Function.Injective (slotIndex : BirthLabel (Torus d m) → ℕ) := by
  intro a b h
  have hdiv := slotIndex_div a
  have hmod := slotIndex_mod a
  rw [h, slotIndex_div] at hdiv
  rw [h, slotIndex_mod] at hmod
  have hk := kindIndex_lt a.kind
  have hk' := kindIndex_lt b.kind
  have hs : a.scale = b.scale := by omega
  have hkind : a.kind = b.kind := kindIndex_injective (by omega)
  have hanchor : a.anchor = b.anchor := (siteRank d m).injective (Fin.ext hmod.symm)
  cases a; cases b; simp_all

/-- Chronology: a slot of a smaller scale comes earlier. -/
theorem slotIndex_lt_of_scale_lt {d m : ℕ} {a b : BirthLabel (Torus d m)}
    (h : a.scale < b.scale) : slotIndex a < slotIndex b := by
  have h1 : slotIndex a < (4 * a.scale + 4) * siteCount d m := by
    unfold slotIndex
    have := (siteRank d m a.anchor).isLt
    have := kindIndex_lt a.kind
    nlinarith
  have h2 : (4 * a.scale + 4) * siteCount d m ≤ slotIndex b := by
    unfold slotIndex
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.le_add_right _ _)
  omega

/-- Within one scale, tile slots precede clearing slots. -/
theorem slotIndex_tile_lt_clearing {d m : ℕ} (j : ℕ) (x y : Torus d m) :
    slotIndex (⟨j, .tile, x⟩ : BirthLabel (Torus d m)) <
      slotIndex (⟨j, .clearing, y⟩ : BirthLabel (Torus d m)) := by
  unfold slotIndex
  simp only [kindIndex]
  have := (siteRank d m x).isLt
  nlinarith

/-- The late tile slots: digit sweeps into stages after the cutoff, and the final residual
sweep (stage `m+1`). -/
def lateSlots (d m : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Ioc (m / 2) (m + 1)) ×ˢ (Finset.univ : Finset (Torus d m))).image
    (fun p => slotIndex (⟨p.1, .tile, p.2⟩ : BirthLabel (Torus d m)))

theorem lateSlots_scale (d m : ℕ) : ∀ n ∈ lateSlots d m, m / 2 ≤ slotScaleOf d m n := by
  classical
  intro n hn
  unfold lateSlots at hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  rw [slotScaleOf_slotIndex]
  exact (Finset.mem_Ioc.mp (Finset.mem_product.mp hp).1).1.le

theorem lateSlots_card (d m : ℕ) :
    ((lateSlots d m).card : ℝ) ≤ 1 * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m) := by
  classical
  unfold lateSlots
  have hcard : Fintype.card (Torus d m) = 4 ^ (20 * d * m) := by
    rw [OAI.Anderson.torus_card, OAI.Anderson.sideLength, ← pow_mul]; ring_nf
  have h := Finset.card_image_le (s := (Finset.Ioc (m / 2) (m + 1)) ×ˢ (Finset.univ : Finset (Torus d m)))
    (f := fun p => slotIndex (⟨p.1, .tile, p.2⟩ : BirthLabel (Torus d m)))
  rw [Finset.card_product, Nat.card_Ioc, Finset.card_univ, hcard] at h
  have h' : (((Finset.Ioc (m / 2) (m + 1) ×ˢ (Finset.univ : Finset (Torus d m))).image
      (fun p => slotIndex (⟨p.1, .tile, p.2⟩ : BirthLabel (Torus d m)))).card : ℝ) ≤
      ((m + 1 - m / 2 : ℕ) : ℝ) * (4 : ℝ) ^ (20 * d * m) := by exact_mod_cast h
  refine le_trans h' ?_
  have : ((m + 1 - m / 2 : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    have : m + 1 - m / 2 ≤ m + 1 := by omega
    exact_mod_cast this
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (20 * d * m) := by positivity
  nlinarith

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The birth label attached to block index `n` (kind 2 = clearing, otherwise tile). -/
def opLabel (d m n : ℕ) : BirthLabel (Torus d m) :=
  ⟨n / (4 * siteCount d m), if (n / siteCount d m) % 4 = 2 then .clearing else .tile,
    (siteRank d m).symm ⟨n % siteCount d m, Nat.mod_lt _ (siteCount_pos d m)⟩⟩

theorem opIndex_div (d m j k : ℕ) (x : Torus d m) :
    opIndex d m j k x / siteCount d m = 4 * j + k := by
  unfold opIndex
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (siteCount_pos d m),
    Nat.div_eq_of_lt (siteRank d m x).isLt, zero_add]

theorem opIndex_mod (d m j k : ℕ) (x : Torus d m) :
    opIndex d m j k x % siteCount d m = (siteRank d m x).val := by
  unfold opIndex
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (siteRank d m x).isLt]

theorem opLabel_opIndex (d m j k : ℕ) (x : Torus d m) (hk : k < 4) :
    opLabel d m (opIndex d m j k x) =
      ⟨j, if k = 2 then .clearing else .tile, x⟩ := by
  have hdiv := opIndex_div d m j k x
  have hmod := opIndex_mod d m j k x
  unfold opLabel
  have h1 : opIndex d m j k x / (4 * siteCount d m) = j := by
    rw [Nat.mul_comm 4, ← Nat.div_div_eq_div_mul, hdiv]; omega
  have h2 : (opIndex d m j k x / siteCount d m) % 4 = k := by rw [hdiv]; omega
  simp only [h1, h2]
  congr 1
  apply (siteRank d m).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext hmod

/-- Tile and clearing blocks carry the label whose slot is the block itself. -/
theorem slotIndex_opLabel (d m j : ℕ) (x : Torus d m) (k : ℕ) (hk : k = 0 ∨ k = 2) :
    slotIndex (opLabel d m (opIndex d m j k x)) = opIndex d m j k x := by
  rw [opLabel_opIndex d m j k x (by omega), slotIndex_eq_opIndex]
  rcases hk with rfl | rfl <;> simp [kindIndex]

/-- The label scale of every block of stage `j`. -/
theorem opLabel_scale (d m j n : ℕ) (h1 : 4 * j * siteCount d m ≤ n)
    (h2 : n < 4 * (j + 1) * siteCount d m) : (opLabel d m n).scale = j := by
  show n / (4 * siteCount d m) = j
  apply Nat.div_eq_of_lt_le
  · calc j * (4 * siteCount d m) = 4 * j * siteCount d m := by ring
      _ ≤ n := h1
  · calc n < 4 * (j + 1) * siteCount d m := h2
      _ = (j + 1) * (4 * siteCount d m) := by ring

end AndersonAC.AgentS78
