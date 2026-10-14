import AndersonAC.S3.Definitions

/-!
Elementary grid facts for §3: one-dimensional grid angles of integer casts, the
additivity of grid angles modulo `2π`, and a lower bound for the number of grid
angles in an interval (the counting input of the direct grid gap).
-/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

/-- The one-dimensional grid angle of a residue. -/
def angle1 (L : ℕ) (x : ZMod L) : ℝ :=
  2 * Real.pi * (if 2 * x.val < L then (x.val : ℝ) else (x.val : ℝ) - (L : ℝ)) / (L : ℝ)

theorem gridAngle_apply {d L : ℕ} [NeZero L] (k : Torus d L) (j : Fin d) :
    gridAngle k j = angle1 L (k j) := rfl

theorem angle1_intCast {L : ℕ} [NeZero L] (m : ℤ) (h1 : -(L : ℤ) ≤ 2 * m) (h2 : 2 * m < L) :
    angle1 L (m : ZMod L) = 2 * Real.pi * m / L := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hv := ZMod.val_intCast (n := L) m
  unfold angle1
  rcases le_or_gt 0 m with hm | hm
  · have hmod : m % (L : ℤ) = m := Int.emod_eq_of_lt hm (by omega)
    rw [hmod] at hv
    have hv' : 2 * (m : ZMod L).val < L := by omega
    rw [if_pos hv']
    have : ((m : ZMod L).val : ℝ) = (m : ℝ) := by exact_mod_cast hv
    rw [this]
  · have hmod : m % (L : ℤ) = m + L := by
      rw [← Int.add_mul_emod_self_right m 1 L, one_mul]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod] at hv
    have hv' : ¬ 2 * (m : ZMod L).val < L := by omega
    rw [if_neg hv']
    have : ((m : ZMod L).val : ℝ) = (m : ℝ) + L := by exact_mod_cast hv
    rw [this]
    ring

theorem angle1_bounds {L : ℕ} [NeZero L] (x : ZMod L) :
    -Real.pi ≤ angle1 L x ∧ angle1 L x < Real.pi := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx := x.val_lt
  unfold angle1
  split_ifs with h
  · constructor
    · have : (0 : ℝ) ≤ 2 * Real.pi * (x.val : ℝ) / L := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ hL]
      have : (2 * x.val : ℝ) < L := by exact_mod_cast h
      nlinarith [Real.pi_pos]
  · push Not at h
    have h' : (L : ℝ) ≤ 2 * x.val := by exact_mod_cast h
    have hx' : (x.val : ℝ) < L := by exact_mod_cast hx
    constructor
    · rw [le_div_iff₀ hL]
      nlinarith [Real.pi_pos]
    · rw [div_lt_iff₀ hL]
      nlinarith [Real.pi_pos]

/-- Grid angles add modulo `2π`. -/
theorem angle1_add {L : ℕ} [NeZero L] (x y : ZMod L) :
    ∃ n : ℤ, angle1 L (x + y) = angle1 L x + angle1 L y + 2 * Real.pi * n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- each angle is `2π (val - L·εᵢ)/L` with `εᵢ ∈ {0,1}`; the sum's val is `vx + vy - L·δ`
  have key : ∀ z : ZMod L, ∃ e : ℤ, angle1 L z = 2 * Real.pi * ((z.val : ℝ) - L * e) / L := by
    intro z
    unfold angle1
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨e1, h1⟩ := key x
  obtain ⟨e2, h2⟩ := key y
  obtain ⟨e3, h3⟩ := key (x + y)
  have hv : ((x + y).val : ℤ) = ((x.val + y.val : ℕ) : ℤ) % L := by
    rw [ZMod.val_add]; push_cast; rfl
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ((x + y).val : ℤ) = x.val + y.val - L * q :=
    ⟨((x.val + y.val : ℕ) : ℤ) / L, by rw [hv, Int.emod_def]; push_cast; ring⟩
  refine ⟨e1 + e2 - e3 - q, ?_⟩
  rw [h1, h2, h3]
  have hq' : ((x + y).val : ℝ) = x.val + y.val - L * q := by exact_mod_cast hq
  rw [hq']
  push_cast
  field_simp
  ring

/-- At least `λL/π - 1` grid angles lie within `λ` of `c`, if `|c| + λ ≤ 3`. -/
theorem card_angle1_near {L : ℕ} [NeZero L] (c lam : ℝ) (hlam : 0 ≤ lam)
    (hc : |c| + lam ≤ 3) :
    lam * L / Real.pi - 1 ≤
      ((Finset.univ.filter fun x : ZMod L => |angle1 L x - c| ≤ lam).card : ℝ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  set lo : ℤ := ⌈(c - lam) * L / (2 * Real.pi)⌉ with hlo
  set hi : ℤ := ⌊(c + lam) * L / (2 * Real.pi)⌋ with hhi
  have hcabs := abs_le.mp (show |c| ≤ 3 - lam by linarith)
  -- every integer of `[lo, hi]` gives a grid angle in the window
  have hrange : ∀ m ∈ Finset.Icc lo hi, -(L : ℤ) ≤ 2 * m ∧ 2 * m < L := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have e1 : (c - lam) * L / (2 * Real.pi) ≤ m := (Int.ceil_le.mp hm1)
    have e2 : (m : ℝ) ≤ (c + lam) * L / (2 * Real.pi) := Int.le_floor.mp hm2
    have f1 : -(3 : ℝ) * L ≤ (c - lam) * L := by nlinarith
    have f2 : (c + lam) * L ≤ 3 * L := by nlinarith
    have g1 : -(L : ℝ) < 2 * m := by
      have : -(3 : ℝ) * L / (2 * Real.pi) ≤ m :=
        le_trans (div_le_div_of_nonneg_right f1 (by positivity)) e1
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have g2 : (2 * m : ℝ) < L := by
      have : (m : ℝ) ≤ 3 * L / (2 * Real.pi) :=
        le_trans e2 (div_le_div_of_nonneg_right f2 (by positivity))
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    constructor
    · exact_mod_cast g1.le
    · exact_mod_cast g2
  have hmaps : ∀ m ∈ Finset.Icc lo hi,
      (m : ZMod L) ∈ Finset.univ.filter fun x : ZMod L => |angle1 L x - c| ≤ lam := by
    intro m hm
    obtain ⟨r1, r2⟩ := hrange m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have e1 : (c - lam) * L / (2 * Real.pi) ≤ m := (Int.ceil_le.mp hm1)
    have e2 : (m : ℝ) ≤ (c + lam) * L / (2 * Real.pi) := Int.le_floor.mp hm2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [angle1_intCast m r1 r2, abs_le]
    rw [div_le_iff₀ (by positivity)] at e1
    rw [le_div_iff₀ (by positivity)] at e2
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hL]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hL]; nlinarith
  have hinj : Set.InjOn (fun m : ℤ => (m : ZMod L)) (Finset.Icc lo hi : Set ℤ) := by
    intro m₁ hm₁ m₂ hm₂ h
    have a1 := angle1_intCast (L := L) m₁ (hrange m₁ hm₁).1 (hrange m₁ hm₁).2
    have a2 := angle1_intCast (L := L) m₂ (hrange m₂ hm₂).1 (hrange m₂ hm₂).2
    simp only at h
    rw [h] at a1
    rw [a1] at a2
    have : (m₁ : ℝ) = m₂ := by
      have := a2
      field_simp at this
      linarith
    exact_mod_cast this
  have hcard := Finset.card_le_card_of_injOn (fun m : ℤ => (m : ZMod L)) hmaps hinj
  have hIcc : ((hi + 1 - lo : ℤ) : ℝ) ≤ ((Finset.Icc lo hi).card : ℝ) := by
    rw [Int.card_Icc]
    exact_mod_cast Int.self_le_toNat _
  have hlo' : (lo : ℝ) < (c - lam) * L / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  have hhi' : (c + lam) * L / (2 * Real.pi) - 1 < hi := by
    have := Int.lt_floor_add_one ((c + lam) * L / (2 * Real.pi)); linarith
  have hdiff : (c + lam) * L / (2 * Real.pi) - (c - lam) * L / (2 * Real.pi) =
      lam * L / Real.pi := by field_simp; ring
  have hcast : ((Finset.Icc lo hi).card : ℝ) ≤
      ((Finset.univ.filter fun x : ZMod L => |angle1 L x - c| ≤ lam).card : ℝ) := by
    exact_mod_cast hcard
  push_cast at hIcc
  linarith

end AndersonAC.S3
