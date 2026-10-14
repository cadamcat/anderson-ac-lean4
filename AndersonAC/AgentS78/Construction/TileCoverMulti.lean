import AndersonAC.AgentS78.Construction.TileCoverBox

/-!
# the §5 tile covers — the cube tiling of the torus. Tiles of side `L` (`L ∣ N`, `5L ≤ N`, `N = sideLength m`), the
concentric cubes `Q` (side `3L`) and `Q'` (side `5L`) and the cutoff `χ` of 05:240–245, in
offset coordinates relative to the corner of `Q'`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem side_pos (m : ℕ) : 0 < OAI.Anderson.sideLength m := Nat.pos_of_ne_zero (NeZero.ne _)

/-- Offset of `x` in coordinate `k` from the corner of the outer cube of the tile with coarse
coordinates `g` (side `L`): the outer cube is `{x | ∀ k, boxOff < 5L}`. -/
def boxOff (L : ℕ) (g : Fin d → ℕ) (x : Torus d m) (k : Fin d) : ℕ :=
  ((x k).val + (2 * L + (OAI.Anderson.sideLength m - g k * L))) % OAI.Anderson.sideLength m

/-- The point with offsets `w`. -/
def boxMap (L : ℕ) (g : Fin d → ℕ) (w : Fin d → ℕ) : Torus d m :=
  fun k => ((w k + g k * L + (OAI.Anderson.sideLength m - 2 * L) : ℕ) : ZMod (OAI.Anderson.sideLength m))

section Arith
variable (L : ℕ) (g : Fin d → ℕ)

theorem boxOff_lt (x : Torus d m) (k : Fin d) : boxOff L g x k < OAI.Anderson.sideLength m :=
  Nat.mod_lt _ (side_pos m)

theorem boxOff_boxMap (h2L : 2 * L ≤ OAI.Anderson.sideLength m) (hg : ∀ k, g k * L ≤ OAI.Anderson.sideLength m)
    (w : Fin d → ℕ) (hw : ∀ k, w k < OAI.Anderson.sideLength m) (k : Fin d) :
    boxOff L g (boxMap (m := m) L g w) k = w k := by
  unfold boxOff boxMap
  rw [ZMod.val_natCast, Nat.mod_add_mod]
  have : w k + g k * L + (OAI.Anderson.sideLength m - 2 * L) + (2 * L + (OAI.Anderson.sideLength m - g k * L)) = w k + 2 * OAI.Anderson.sideLength m := by
    have := hg k; omega
  rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hw k)]

theorem boxMap_boxOff (h2L : 2 * L ≤ OAI.Anderson.sideLength m) (hg : ∀ k, g k * L ≤ OAI.Anderson.sideLength m) (x : Torus d m) :
    boxMap (m := m) L g (boxOff L g x) = x := by
  funext k
  unfold boxMap boxOff
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_mod, ← Nat.cast_add, ← Nat.cast_add]
  have : (x k).val + (2 * L + (OAI.Anderson.sideLength m - g k * L)) + g k * L + (OAI.Anderson.sideLength m - 2 * L) =
      (x k).val + 2 * OAI.Anderson.sideLength m := by
    have := hg k; omega
  rw [this]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

/-- Coordinates of a point in terms of its offsets. -/
theorem coord_eq_offset (h2L : 2 * L ≤ OAI.Anderson.sideLength m) (hg : ∀ k, g k * L ≤ OAI.Anderson.sideLength m) (x : Torus d m)
    (k : Fin d) : x k = ((boxOff L g x k : ℕ) : ZMod (OAI.Anderson.sideLength m)) +
      ((g k * L + (OAI.Anderson.sideLength m - 2 * L) : ℕ) : ZMod (OAI.Anderson.sideLength m)) := by
  conv_lhs => rw [← boxMap_boxOff L g h2L hg x]
  unfold boxMap
  push_cast
  ring

theorem boxOff_add_basis (h2 : 2 ≤ OAI.Anderson.sideLength m) (x : Torus d m) (i k : Fin d) :
    boxOff L g (x + OAI.Anderson.torusBasisVector i) k =
      if k = i then (boxOff L g x k + 1) % OAI.Anderson.sideLength m else boxOff L g x k := by
  unfold boxOff OAI.Anderson.torusBasisVector
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, Pi.add_apply, Pi.single_eq_same, ZMod.val_add, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < OAI.Anderson.sideLength m), Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    ring
  · rw [if_neg hki, Pi.add_apply, Pi.single_eq_of_ne hki, add_zero]

theorem boxOff_of_tile (h3L : 3 * L ≤ OAI.Anderson.sideLength m) (hL : 0 < L) (x : Torus d m) (k : Fin d)
    (hx : (x k).val / L = g k) : boxOff L g x k = 2 * L + (x k).val % L := by
  unfold boxOff
  have hdm : L * g k + (x k).val % L = (x k).val := by rw [← hx]; exact Nat.div_add_mod _ _
  have hlt := ZMod.val_lt (x k)
  have hmod := Nat.mod_lt (x k).val hL
  rw [Nat.mul_comm] at hdm
  generalize g k * L = G at hdm ⊢
  have : (x k).val + (2 * L + (OAI.Anderson.sideLength m - G)) =
      (2 * L + (x k).val % L) + OAI.Anderson.sideLength m := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem boxOff_mod (hLN : L ∣ OAI.Anderson.sideLength m) (hg : ∀ k, g k * L ≤ OAI.Anderson.sideLength m) (x : Torus d m)
    (k : Fin d) : boxOff L g x k % L = (x k).val % L := by
  unfold boxOff
  rw [Nat.mod_mod_of_dvd _ hLN]
  obtain ⟨M, hM⟩ := hLN
  have hgk := hg k
  have : 2 * L + (OAI.Anderson.sideLength m - g k * L) = L * (2 + (M - g k)) := by
    rw [hM] at hgk ⊢
    rw [Nat.mul_add, Nat.mul_sub, mul_comm (g k) L]
    have : L * g k ≤ L * M := by rw [mul_comm L (g k)]; exact hgk
    omega
  rw [this, Nat.add_mul_mod_self_left]

end Arith

/-! ## Circular distances of differences -/

theorem circDist_cast_sub (a b : ℕ) (ha : a < OAI.Anderson.sideLength m) (hb : b < OAI.Anderson.sideLength m) :
    circDist m ((a : ZMod (OAI.Anderson.sideLength m)) - (b : ZMod (OAI.Anderson.sideLength m))) =
      min (if b ≤ a then a - b else b - a) (OAI.Anderson.sideLength m - (if b ≤ a then a - b else b - a)) := by
  unfold circDist
  by_cases hab : b ≤ a
  · rw [if_pos hab]
    have : (a : ZMod (OAI.Anderson.sideLength m)) - (b : ZMod (OAI.Anderson.sideLength m)) = ((a - b : ℕ) : ZMod (OAI.Anderson.sideLength m)) := by
      rw [Nat.cast_sub hab]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hab]
    have : (a : ZMod (OAI.Anderson.sideLength m)) - (b : ZMod (OAI.Anderson.sideLength m)) =
        ((OAI.Anderson.sideLength m - (b - a) : ℕ) : ZMod (OAI.Anderson.sideLength m)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
      ring
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [min_comm]
    congr 1
    omega


/-! ## The cutoff -/

/-- Truncated distance of an offset to the inner range `[L, 4L)`. -/
def cutDelta (L o : ℕ) : ℕ :=
  min L (if o < L then L - o else if o < 4 * L then 0 else o + 1 - 4 * L)

theorem cutDelta_le (L o : ℕ) : cutDelta L o ≤ L := min_le_left _ _

theorem cutDelta_step (L N o : ℕ) (hL : 0 < L) (hN : 5 * L ≤ N) (ho : o < N) :
    cutDelta L o ≤ cutDelta L ((o + 1) % N) + 1 ∧
      cutDelta L ((o + 1) % N) ≤ cutDelta L o + 1 := by
  by_cases h : o + 1 < N
  · rw [Nat.mod_eq_of_lt h]
    unfold cutDelta
    simp only [min_def]
    constructor <;> (split_ifs <;> omega)
  · have : o + 1 = N := by omega
    rw [this, Nat.mod_self]
    unfold cutDelta
    simp only [min_def]
    constructor <;> (split_ifs <;> omega)

/-- `ℓ^∞` truncated distance to the inner cube. -/
def cutD (L : ℕ) (g : Fin d → ℕ) (x : Torus d m) : ℕ :=
  Finset.univ.sup fun k => cutDelta L (boxOff L g x k)

theorem cutD_le (L : ℕ) (g : Fin d → ℕ) (x : Torus d m) : cutD L g x ≤ L :=
  Finset.sup_le fun k _ => cutDelta_le L _

theorem cutD_eq_zero (L : ℕ) (g : Fin d → ℕ) (x : Torus d m)
    (hx : ∀ k, L ≤ boxOff L g x k ∧ boxOff L g x k < 4 * L) : cutD L g x = 0 := by
  unfold cutD
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun k _ => ?_)
  have := hx k
  unfold cutDelta
  simp only [min_def]
  split_ifs <;> omega

theorem cutD_eq_L (L : ℕ) (g : Fin d → ℕ) (x : Torus d m) (k : Fin d)
    (hk : 5 * L ≤ boxOff L g x k) : cutD L g x = L := by
  refine le_antisymm (cutD_le L g x) ?_
  have h : cutDelta L (boxOff L g x k) = L := by
    unfold cutDelta; simp only [min_def]; split_ifs <;> omega
  calc L = cutDelta L (boxOff L g x k) := h.symm
    _ ≤ cutD L g x := Finset.le_sup (f := fun k => cutDelta L (boxOff L g x k))
        (Finset.mem_univ k)

theorem cutD_step (L : ℕ) (g : Fin d → ℕ) (hL : 0 < L)
    (hN : 5 * L ≤ OAI.Anderson.sideLength m) (x : Torus d m) (i : Fin d) :
    cutD L g x ≤ cutD L g (x + OAI.Anderson.torusBasisVector i) + 1 ∧
      cutD L g (x + OAI.Anderson.torusBasisVector i) ≤ cutD L g x + 1 := by
  have h2 : 2 ≤ OAI.Anderson.sideLength m := by omega
  have hk : ∀ k, cutDelta L (boxOff L g x k) ≤
        cutDelta L (boxOff L g (x + OAI.Anderson.torusBasisVector i) k) + 1 ∧
      cutDelta L (boxOff L g (x + OAI.Anderson.torusBasisVector i) k) ≤
        cutDelta L (boxOff L g x k) + 1 := by
    intro k
    rw [boxOff_add_basis L g h2 x i k]
    split_ifs
    · exact cutDelta_step L _ _ hL hN (boxOff_lt L g x k)
    · omega
  constructor
  · refine Finset.sup_le fun k _ => le_trans (hk k).1 ?_
    exact Nat.add_le_add_right (Finset.le_sup (f := fun k => cutDelta L
      (boxOff L g (x + OAI.Anderson.torusBasisVector i) k)) (Finset.mem_univ k)) 1
  · refine Finset.sup_le fun k _ => le_trans (hk k).2 ?_
    exact Nat.add_le_add_right (Finset.le_sup (f := fun k => cutDelta L
      (boxOff L g x k)) (Finset.mem_univ k)) 1


/-! ## Adjacency -/

theorem adj_add_basis (h2 : 2 ≤ OAI.Anderson.sideLength m) (x : Torus d m) (i : Fin d) :
    (nnGraph d m).Adj x (x + OAI.Anderson.torusBasisVector i) := by
  refine (nn_adj_iff _ _).2 ⟨fun h => ?_, i, Or.inl rfl⟩
  have h1 := congrFun h i
  simp only [Pi.add_apply, OAI.Anderson.torusBasisVector, Pi.single_eq_same] at h1
  have h3 : (1 : ZMod (OAI.Anderson.sideLength m)) = 0 := by
    have := congrArg (fun z => z - x i) h1
    simp only [sub_self, add_sub_cancel_left] at this
    exact this.symm
  have h4 := congrArg ZMod.val h3
  rw [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at h4
  exact one_ne_zero h4

/-! ## The tiling -/

/-- Coarse coordinates of tile `T`. -/
def gOf {M : ℕ} (T : Fin (M ^ d)) : Fin d → ℕ := fun k => (finFunctionFinEquiv.symm T k).val

/-- The cube tiling with `M` tiles of side `L` per axis (05:240–245). -/
def multiTiling (M L : ℕ) : TorusTiling d m where
  count := M ^ d
  tile T := Finset.univ.filter fun x => ∀ k, (x k).val / L = gOf T k
  inner T := Finset.univ.filter fun x => ∀ k, L ≤ boxOff L (gOf T) x k ∧ boxOff L (gOf T) x k < 4 * L
  outer T := Finset.univ.filter fun x => ∀ k, boxOff L (gOf T) x k < 5 * L
  cutoff T x := 1 - (cutD L (gOf T) x : ℝ) / L

section Multi
variable (M L : ℕ) (hML : OAI.Anderson.sideLength m = M * L) (hL : 0 < L) (h5 : 5 ≤ M)
include hML hL h5

theorem gOf_mul_le (T : Fin (M ^ d)) (k : Fin d) :
    gOf T k * L + L ≤ OAI.Anderson.sideLength m := by
  have h := (finFunctionFinEquiv.symm T k).isLt
  rw [hML]
  have : gOf T k + 1 ≤ M := h
  nlinarith

theorem five_L_le : 5 * L ≤ OAI.Anderson.sideLength m := by rw [hML]; nlinarith

/-- The outer cube is the image of the grid box of side `5L`. -/
theorem multi_outer_eq (T : Fin (M ^ d)) :
    (multiTiling (m := m) M L).outer T =
      Finset.univ.image fun w : Fin d → Fin (5 * L) => boxMap (m := m) L (gOf T)
        (fun k => (w k).val) := by
  have h2L : 2 * L ≤ OAI.Anderson.sideLength m := by have := five_L_le (m := m) M L hML hL h5; omega
  have hg : ∀ k, gOf T k * L ≤ OAI.Anderson.sideLength m := fun k => by
    have := gOf_mul_le (m := m) M L hML hL h5 T k; omega
  ext x
  simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨fun k => ⟨boxOff L (gOf T) x k, hx k⟩, ?_⟩
    exact boxMap_boxOff L (gOf T) h2L hg x
  · rintro ⟨w, rfl⟩ k
    rw [boxOff_boxMap L (gOf T) h2L hg _ (fun k => by
      have := (w k).isLt; have := five_L_le (m := m) M L hML hL h5; omega) k]
    exact (w k).isLt


theorem multi_axioms (hGP : GridPoincareStatement) (hMet : TorusMetricStatement) (t : ℝ)
    (hLt : S45.power t (-6) ≤ L) :
    TilingAxioms (multiTiling (d := d) (m := m) M L) t (5 ^ d + 50 * d) (((5 * L : ℕ) : ℝ) ^ d)
      (1 / L) (2 * d * ((5 * L : ℕ) : ℝ) ^ 2) := by
  classical
  have h5L := five_L_le (m := m) M L hML hL h5
  have h2L : 2 * L ≤ OAI.Anderson.sideLength m := by omega
  have h3L : 3 * L ≤ OAI.Anderson.sideLength m := by omega
  have h2 : 2 ≤ OAI.Anderson.sideLength m := by omega
  have hg : ∀ (T : Fin (M ^ d)) k, gOf T k * L ≤ OAI.Anderson.sideLength m := fun T k => by
    have := gOf_mul_le (m := m) M L hML hL h5 T k; omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h5d : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  refine
    { partition := ?_
      tile_inner := ?_
      inner_outer := ?_
      outer_nonempty := ?_
      buffer := ?_
      overlap := ?_
      outer_card := ?_
      cutoff_nonneg := ?_
      cutoff_le_one := ?_
      cutoff_one := ?_
      cutoff_zero := ?_
      lip := ?_
      poincare := ?_
      ell_nonneg := by positivity
      pc_nonneg := by positivity
      lip_pc := ?_ }
  · -- partition
    intro x
    let q : Fin d → Fin M := fun k => ⟨(x k).val / L, by
        rw [Nat.div_lt_iff_lt_mul hL, ← hML]; exact ZMod.val_lt _⟩
    refine ⟨finFunctionFinEquiv q, ?_, ?_⟩
    · simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and, gOf,
        Equiv.symm_apply_apply, q, implies_true]
    · intro T hT
      simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      apply finFunctionFinEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      funext k
      exact Fin.ext (hT k).symm
  · -- tile ⊆ inner
    intro T x hx
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro k
    rw [boxOff_of_tile L (gOf T) h3L hL x k (hx k)]
    have := Nat.mod_lt (x k).val hL
    omega
  · -- inner ⊆ outer
    intro T x hx
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro k; have := hx k; omega
  · -- outer nonempty
    intro T
    refine ⟨boxMap L (gOf T) (fun _ => 0), ?_⟩
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    rw [boxOff_boxMap L (gOf T) h2L (hg T) _ (fun _ => side_pos m) k]
    omega
  · -- buffer
    intro T x hx y hy
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    push Not at hy
    obtain ⟨k, hk⟩ := hy
    have hterm : L + 1 ≤ circDist m (x k - y k) := by
      rw [coord_eq_offset L (gOf T) h2L (hg T) x k, coord_eq_offset L (gOf T) h2L (hg T) y k,
        add_sub_add_right_eq_sub, circDist_cast_sub _ _ (boxOff_lt L _ x k) (boxOff_lt L _ y k)]
      have ha := boxOff_of_tile L (gOf T) h3L hL x k (hx k)
      have hr := Nat.mod_lt (x k).val hL
      have hb := boxOff_lt L (gOf T) y k
      simp only [min_def]
      split_ifs <;> omega
    have hsum : circDist m (x k - y k) ≤ l1Dist y x :=
      Finset.single_le_sum (f := fun k => circDist m (x k - y k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    rw [hMet]
    calc S45.power t (-6) ≤ L := hLt
      _ ≤ ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ (l1Dist y x : ℝ) := by exact_mod_cast hterm.trans hsum
  · -- overlap
    intro x
    let φ : Fin (M ^ d) → (Fin d → Fin 5) := fun T k =>
      ⟨min (boxOff L (gOf T) x k / L) 4, by omega⟩
    have hinj : ∀ T T' : Fin (M ^ d), (∀ k, boxOff L (gOf T) x k < 5 * L) →
        (∀ k, boxOff L (gOf T') x k < 5 * L) → φ T = φ T' → T = T' := by
      intro T T' hT hT' heq
      have hoff : ∀ k, boxOff L (gOf T) x k = boxOff L (gOf T') x k := by
        intro k
        have h1 := congrArg Fin.val (congrFun heq k)
        simp only [φ] at h1
        have hd1 : boxOff L (gOf T) x k / L < 5 := by
          rw [Nat.div_lt_iff_lt_mul hL]; have := hT k; omega
        have hd2 : boxOff L (gOf T') x k / L < 5 := by
          rw [Nat.div_lt_iff_lt_mul hL]; have := hT' k; omega
        rw [min_eq_left (by omega), min_eq_left (by omega)] at h1
        have hm1 := boxOff_mod L (gOf T) ⟨M, by rw [hML, mul_comm]⟩ (hg T) x k
        have hm2 := boxOff_mod L (gOf T') ⟨M, by rw [hML, mul_comm]⟩ (hg T') x k
        rw [← Nat.div_add_mod (boxOff L (gOf T) x k) L,
          ← Nat.div_add_mod (boxOff L (gOf T') x k) L, h1, hm1, hm2]
      apply finFunctionFinEquiv.symm.injective
      funext k
      apply Fin.ext
      have e1 := coord_eq_offset L (gOf T) h2L (hg T) x k
      have e2 := coord_eq_offset L (gOf T') h2L (hg T') x k
      rw [hoff k] at e1
      have e3 := e1.symm.trans e2
      have e4 := add_left_cancel e3
      rw [ZMod.natCast_eq_natCast_iff'] at e4
      have e5 : gOf T k * L % OAI.Anderson.sideLength m =
          gOf T' k * L % OAI.Anderson.sideLength m :=
        Nat.ModEq.add_right_cancel' (OAI.Anderson.sideLength m - 2 * L) e4
      rw [Nat.mod_eq_of_lt (by have := gOf_mul_le (m := m) M L hML hL h5 T k; omega),
        Nat.mod_eq_of_lt (by have := gOf_mul_le (m := m) M L hML hL h5 T' k; omega)] at e5
      exact Nat.eq_of_mul_eq_mul_right hL e5
    refine le_trans (b := (((5 : ℕ) ^ d : ℕ) : ℝ)) ?_ (by push_cast; linarith)
    norm_cast
    refine le_trans (Finset.card_le_card_of_injOn φ (by intro a _; exact Finset.mem_univ _) ?_)
      (by simp)
    intro T hT T' hT' heq
    exact hinj T T' (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hT')).2).2 heq
  · -- outer card
    intro T
    rw [multi_outer_eq (m := m) M L hML hL h5 T]
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin d → Fin (5 * L))))
      (f := fun w : Fin d → Fin (5 * L) => boxMap (m := m) L (gOf T) (fun k => (w k).val))
    have hu : (Finset.univ : Finset (Fin d → Fin (5 * L))).card = (5 * L) ^ d := by simp
    rw [hu] at this
    exact_mod_cast this
  · -- cutoff ≥ 0
    intro T x
    have := cutD_le L (gOf T) x
    simp only [multiTiling]
    have : (cutD L (gOf T) x : ℝ) / L ≤ 1 := by
      rw [div_le_one hLr]; exact_mod_cast this
    linarith
  · -- cutoff ≤ 1
    intro T x
    simp only [multiTiling]
    have : 0 ≤ (cutD L (gOf T) x : ℝ) / L := by positivity
    linarith
  · -- cutoff = 1 on Q
    intro T x hx
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [cutD_eq_zero L (gOf T) x hx]; simp
  · -- cutoff = 0 off Q'
    intro T x hx
    simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    rw [cutD_eq_L L (gOf T) x k hk, div_self hLr.ne']; ring
  · -- Lipschitz
    intro T x y hxy
    simp only [multiTiling]
    have key : ∀ a b : Torus d m, ∀ i : Fin d, b = a + OAI.Anderson.torusBasisVector i →
        |(1 - (cutD L (gOf T) a : ℝ) / L) - (1 - (cutD L (gOf T) b : ℝ) / L)| ≤ 1 / L := by
      intro a b i hb
      subst hb
      obtain ⟨h1, h2⟩ := cutD_step L (gOf T) hL h5L a i
      have h1' : (cutD L (gOf T) a : ℝ) ≤ cutD L (gOf T) (a + OAI.Anderson.torusBasisVector i) + 1 := by
        exact_mod_cast h1
      have h2' : (cutD L (gOf T) (a + OAI.Anderson.torusBasisVector i) : ℝ) ≤ cutD L (gOf T) a + 1 := by
        exact_mod_cast h2
      rw [show (1 - (cutD L (gOf T) a : ℝ) / L) - (1 - (cutD L (gOf T)
          (a + OAI.Anderson.torusBasisVector i) : ℝ) / L) =
          ((cutD L (gOf T) (a + OAI.Anderson.torusBasisVector i) : ℝ) - cutD L (gOf T) a) / L by
        ring, abs_div, abs_of_pos hLr]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hLr.le
    obtain ⟨-, i, hi | hi⟩ := (nn_adj_iff x y).1 hxy
    · exact key x y i hi
    · have hx : x = y + OAI.Anderson.torusBasisVector i := by rw [hi]; abel
      rw [abs_sub_comm]; exact key y x i hx
  · -- Poincaré
    intro T v
    rw [multi_outer_eq (m := m) M L hML hL h5 T]
    have hb := poincare_of_box hGP (K := 5 * L)
      (fun w : Fin d → Fin (5 * L) => boxMap (m := m) L (gOf T) (fun k => (w k).val)) ?_ ?_ v
    · exact_mod_cast hb
    · intro w w' h
      funext k
      apply Fin.ext
      have h1 := congrArg (fun x => boxOff L (gOf T) x k) h
      simp only at h1
      have hw : ∀ (u : Fin d → Fin (5 * L)) k, (u k).val < OAI.Anderson.sideLength m :=
        fun u k => by have := (u k).isLt; omega
      rwa [boxOff_boxMap L (gOf T) h2L (hg T) _ (hw w) k,
        boxOff_boxMap L (gOf T) h2L (hg T) _ (hw w') k] at h1
    · intro w i hi
      have heq : boxMap (m := m) L (gOf T) (fun k => (gridStep w i k).val) =
          boxMap (m := m) L (gOf T) (fun k => (w k).val) + OAI.Anderson.torusBasisVector i := by
        funext k
        simp only [boxMap, gridStep, Pi.add_apply, OAI.Anderson.torusBasisVector]
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self, dif_pos hi, Pi.single_eq_same]
          push_cast; ring
        · rw [Function.update_of_ne hki, Pi.single_eq_of_ne hki, add_zero]
      rw [heq]
      exact adj_add_basis h2 _ i
  · -- lip_pc
    have : (1 / (L : ℝ)) ^ 2 * (2 * d * ((5 * L : ℕ) : ℝ) ^ 2) = 50 * d := by
      push_cast; field_simp; ring
    rw [this]; linarith


theorem multi_diam (hMet : TorusMetricStatement) (T : Fin (M ^ d)) (x y : Torus d m)
    (hx : x ∈ (multiTiling (m := m) M L).tile T) (hy : y ∈ (multiTiling (m := m) M L).tile T) :
    physicalDistance d m x y ≤ d * L := by
  simp only [multiTiling, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rw [hMet]
  have hk : ∀ k, circDist m (y k - x k) ≤ L := by
    intro k
    have e1 : y k = (((y k).val : ℕ) : ZMod (OAI.Anderson.sideLength m)) :=
      (ZMod.natCast_zmod_val _).symm
    have e2 : x k = (((x k).val : ℕ) : ZMod (OAI.Anderson.sideLength m)) :=
      (ZMod.natCast_zmod_val _).symm
    rw [e1, e2, circDist_cast_sub _ _ (ZMod.val_lt _) (ZMod.val_lt _)]
    have h1 := Nat.div_add_mod (x k).val L
    have h2 := Nat.div_add_mod (y k).val L
    have h3 := Nat.mod_lt (x k).val hL
    have h4 := Nat.mod_lt (y k).val hL
    rw [hx k] at h1
    rw [hy k] at h2
    generalize L * gOf T k = G at h1 h2
    simp only [min_def]
    split_ifs <;> omega
  have hsum : l1Dist x y ≤ d * L := by
    unfold l1Dist
    calc ∑ k, circDist m (y k - x k) ≤ ∑ _k : Fin d, L := Finset.sum_le_sum fun k _ => hk k
      _ = d * L := by simp
  exact_mod_cast hsum

end Multi

/-! ## The single-tile regime (small torus) -/

/-- One tile: the whole torus, `χ = 1`. -/
def singleTiling : TorusTiling d m where
  count := 1
  tile _ := Finset.univ
  inner _ := Finset.univ
  outer _ := Finset.univ
  cutoff _ _ := 1

theorem single_axioms (hGP : GridPoincareStatement) (t : ℝ) :
    TilingAxioms (singleTiling (d := d) (m := m)) t (5 ^ d + 50 * d)
      ((OAI.Anderson.sideLength m : ℝ) ^ d) 0
      (2 * d * ((OAI.Anderson.sideLength m : ℕ) : ℝ) ^ 2) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h5d : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  let β : (Fin d → Fin (OAI.Anderson.sideLength m)) → Torus d m := fun w k => ((w k).val : ZMod _)
  have himg : (Finset.univ : Finset (Torus d m)) = Finset.univ.image β := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
    exact ⟨fun k => ⟨(x k).val, ZMod.val_lt _⟩, by funext k; simp [β]⟩
  refine
    { partition := fun x => ⟨⟨0, by simp [singleTiling]⟩, Finset.mem_univ _, fun T _ =>
        Fin.ext (by have := T.isLt; have h : (singleTiling (d := d) (m := m)).count = 1 := rfl; simp; omega)⟩
      tile_inner := fun _ => Finset.Subset.refl _
      inner_outer := fun _ => Finset.Subset.refl _
      outer_nonempty := fun _ => Finset.univ_nonempty
      buffer := fun T x _ y hy => absurd (Finset.mem_univ y) hy
      overlap := ?_
      outer_card := ?_
      cutoff_nonneg := fun _ _ => zero_le_one
      cutoff_le_one := fun _ _ => le_refl _
      cutoff_one := fun _ _ _ => rfl
      cutoff_zero := fun T x hx => absurd (Finset.mem_univ x) hx
      lip := fun T x y _ => by simp [singleTiling]
      poincare := ?_
      ell_nonneg := le_refl _
      pc_nonneg := by positivity
      lip_pc := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity }
  · intro x
    have hc : (Fintype.card (Fin (singleTiling (d := d) (m := m)).count) : ℝ) = 1 := by
      have h : (singleTiling (d := d) (m := m)).count = 1 := rfl
      have : Fintype.card (Fin (singleTiling (d := d) (m := m)).count) = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨0, by omega⟩, fun T => Fin.ext (by have := T.isLt; omega)⟩
      exact_mod_cast this
    refine le_trans (Nat.cast_le.2 (Finset.card_le_univ _)) ?_
    rw [hc]; linarith
  · intro T
    show ((Finset.univ : Finset (Torus d m)).card : ℝ) ≤ _
    rw [Finset.card_univ, OAI.Anderson.torus_card]; push_cast; rfl
  · intro T v
    show ∑ x ∈ Finset.univ, _ ≤ _
    rw [show (singleTiling (d := d) (m := m)).outer T = Finset.univ from rfl, himg]
    refine poincare_of_box hGP β ?_ ?_ v
    · intro w w' h
      funext k
      apply Fin.ext
      have := congrArg ZMod.val (congrFun h k)
      simp only [β, ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt (w k).isLt, Nat.mod_eq_of_lt (w' k).isLt] at this
    · intro w i hi
      have heq : β (gridStep w i) = β w + OAI.Anderson.torusBasisVector i := by
        funext k
        simp only [β, gridStep, Pi.add_apply, OAI.Anderson.torusBasisVector]
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self, dif_pos hi, Pi.single_eq_same]
          push_cast; ring
        · rw [Function.update_of_ne hki, Pi.single_eq_of_ne hki, add_zero]
      rw [heq]
      exact adj_add_basis (by omega) _ i

end AndersonAC.AgentS78
