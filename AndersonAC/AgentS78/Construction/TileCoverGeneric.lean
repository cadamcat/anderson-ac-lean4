import AndersonAC.AgentS78.Construction.TileCoverParts
import AndersonAC.S45.FormDualityProof
import AndersonAC.S45.LocalTransferLProof

/-!
# WP10 construction: the §5 tile covers — the generic restriction

agent-s78cover (2026-10-14). From a torus tiling satisfying `TilingAxioms` (partition, nesting,
buffer, bounded overlap of the outer cubes, cardinalities, a cutoff with values in `[0,1]`, one
on `Q`, zero off `Q'`, Lipschitz along edges, and a Poincaré inequality on `Q'` balancing the
Lipschitz constant), the restriction along every injective port family is an `S45.TileCover`
(05:240–291). The analytic torus inputs are the sub-statements of TileCoverParts.lean.
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- Energy of the nearest-neighbour edges inside a set of sites (each unordered edge once). -/
def setEnergy (A : Finset (Torus d m)) (v : Torus d m → ℝ) : ℝ := by
  classical
  exact (1 / 2) * ∑ x ∈ A, ∑ y ∈ A, if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0

/-- Average over a set of sites. -/
def setAvg (A : Finset (Torus d m)) (v : Torus d m → ℝ) : ℝ := (∑ x ∈ A, v x) / A.card

/-- Hypotheses on a torus tiling under which its restrictions are tile covers. -/
structure TilingAxioms (τ : TorusTiling d m) (t A B ℓ Pc : ℝ) : Prop where
  partition : ∀ x, ∃! T, x ∈ τ.tile T
  tile_inner : ∀ T, τ.tile T ⊆ τ.inner T
  inner_outer : ∀ T, τ.inner T ⊆ τ.outer T
  outer_nonempty : ∀ T, (τ.outer T).Nonempty
  buffer : ∀ T, ∀ x ∈ τ.tile T, ∀ y, y ∉ τ.inner T →
    S45.power t (-6) ≤ physicalDistance d m y x
  overlap : ∀ x, ((Finset.univ.filter fun T => x ∈ τ.outer T).card : ℝ) ≤ A
  outer_card : ∀ T, ((τ.outer T).card : ℝ) ≤ B
  cutoff_nonneg : ∀ T x, 0 ≤ τ.cutoff T x
  cutoff_le_one : ∀ T x, τ.cutoff T x ≤ 1
  cutoff_one : ∀ T, ∀ x ∈ τ.inner T, τ.cutoff T x = 1
  cutoff_zero : ∀ T x, x ∉ τ.outer T → τ.cutoff T x = 0
  lip : ∀ T x y, (nnGraph d m).Adj x y → |τ.cutoff T x - τ.cutoff T y| ≤ ℓ
  poincare : ∀ T (v : Torus d m → ℝ),
    ∑ x ∈ τ.outer T, (v x - setAvg (τ.outer T) v) ^ 2 ≤ Pc * setEnergy (τ.outer T) v
  ell_nonneg : 0 ≤ ℓ
  pc_nonneg : 0 ≤ Pc
  lip_pc : ℓ ^ 2 * Pc ≤ A


/-! ## Sums over an injective port family -/

section Ports
variable {P : Type} [Fintype P] [DecidableEq P]

theorem sum_port_le (ι : P → Port d m) (hι : Function.Injective ι) (F : Torus d m → ℝ)
    (hF : ∀ y, 0 ≤ F y) : ∑ j, F (ι j).1 ≤ 2 * ∑ y, F y := by
  classical
  have h1 : ∑ j, F (ι j).1 = ∑ p ∈ Finset.univ.map ⟨ι, hι⟩, F p.1 := by
    rw [Finset.sum_map]; rfl
  have h2 : ∑ p ∈ Finset.univ.map ⟨ι, hι⟩, F p.1 ≤ ∑ p : Port d m, F p.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hF p.1)
  have h3 : ∑ p : Port d m, F p.1 = 2 * ∑ y, F y := by
    show ∑ p : Torus d m × Bool, F p.1 = _
    rw [Fintype.sum_prod_type]
    simp [Fintype.sum_bool, Finset.mul_sum, two_mul]
  linarith

theorem sum_port_pair_le (ι : P → Port d m) (hι : Function.Injective ι)
    (G : Torus d m → Torus d m → ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    ∑ i, ∑ j, G (ι i).1 (ι j).1 ≤ 4 * ∑ x, ∑ y, G x y := by
  have hin : ∀ i, ∑ j, G (ι i).1 (ι j).1 ≤ 2 * ∑ y, G (ι i).1 y :=
    fun i => sum_port_le ι hι (G (ι i).1) (hG _)
  calc ∑ i, ∑ j, G (ι i).1 (ι j).1 ≤ ∑ i, 2 * ∑ y, G (ι i).1 y := Finset.sum_le_sum fun i _ => hin i
    _ = 2 * ∑ i, (fun x => ∑ y, G x y) (ι i).1 := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑ x, ∑ y, G x y) := by
        gcongr
        exact sum_port_le ι hι _ fun x => Finset.sum_nonneg fun y _ => hG x y
    _ = 4 * ∑ x, ∑ y, G x y := by ring

theorem card_filter_port_le (ι : P → Port d m) (hι : Function.Injective ι)
    (A : Finset (Torus d m)) :
    ((Finset.univ.filter fun x : P => (ι x).1 ∈ A).card : ℝ) ≤ 2 * A.card := by
  classical
  have h := sum_port_le ι hι (fun y => if y ∈ A then (1 : ℝ) else 0)
    (fun y => by split_ifs <;> norm_num)
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at h
  exact_mod_cast h

end Ports

/-! ## The local edge energy -/

/-- Nearest-neighbour conductances inside a set of sites. -/
def setEdge (A : Finset (Torus d m)) : S45.RMat A := by
  classical
  exact fun x y => if (nnGraph d m).Adj x.1 y.1 then 1 else 0

/-- Extension by zero of a function on a set of sites. -/
def extendSet (A : Finset (Torus d m)) (v : A → ℝ) : Torus d m → ℝ := fun y =>
  if h : y ∈ A then v ⟨y, h⟩ else 0

theorem setEdge_isSymm (A : Finset (Torus d m)) : (setEdge A).IsSymm := by
  classical
  ext x y
  simp only [Matrix.transpose_apply, setEdge]
  by_cases h : (nnGraph d m).Adj x.1 y.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem setEnergy_nonneg (A : Finset (Torus d m)) (v : Torus d m → ℝ) : 0 ≤ setEnergy A v := by
  classical
  unfold setEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  split_ifs <;> positivity

theorem qform_setEdge (A : Finset (Torus d m)) (v : A → ℝ) :
    S45.qform (S45.laplacian (setEdge A)) v = setEnergy A (extendSet A v) := by
  classical
  rw [AgentS45.qform_eq_neg_half_diff_sum _ (AgentS45.laplacian_isSymm _ (setEdge_isSymm A))
    (AgentS45.laplacian_row_sum _)]
  have hpt : ∀ x y : A, -(1 / 2 : ℝ) * (S45.laplacian (setEdge A) x y * (v x - v y) ^ 2) =
      (1 / 2) * (if (nnGraph d m).Adj x.1 y.1 then (extendSet A v x.1 - extendSet A v y.1) ^ 2
        else 0) := by
    intro x y
    have hx : extendSet A v x.1 = v x := by simp [extendSet, x.2]
    have hy : extendSet A v y.1 = v y := by simp [extendSet, y.2]
    rw [hx, hy]
    by_cases hxy : x = y
    · subst hxy; simp
    · have hl : S45.laplacian (setEdge A) x y = -setEdge A x y := by
        simp [S45.laplacian, hxy]
      rw [hl]
      unfold setEdge
      split_ifs <;> ring
  unfold setEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← hpt x y]


/-! ## Degree, constant kernel and the cutoff energy -/

theorem nn_adj_iff (x y : Torus d m) : (nnGraph d m).Adj x y ↔ x ≠ y ∧
    ∃ i : Fin d, y = x + OAI.Anderson.torusBasisVector i ∨
      y = x - OAI.Anderson.torusBasisVector i := by
  unfold nnGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · obtain ⟨i, hi | hi⟩ := h
      · exact ⟨hne, i, Or.inr (by rw [hi]; abel)⟩
      · exact ⟨hne, i, Or.inl (by rw [hi]; abel)⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

open Classical in
theorem sum_adj_le (x : Torus d m) (c : ℝ) (hc : 0 ≤ c) :
    (∑ y, if (nnGraph d m).Adj x y then c else 0) ≤ 2 * d * c := by
  classical
  have hsub : (Finset.univ.filter ((nnGraph d m).Adj x)) ⊆
      Finset.univ.image (fun p : Fin d × Bool => if p.2 then x + OAI.Anderson.torusBasisVector p.1
        else x - OAI.Anderson.torusBasisVector p.1) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨-, i, hi | hi⟩ := (nn_adj_iff x y).1 hy
    · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [hi]⟩
    · exact Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, by simp [hi]⟩
  have hcard : ((Finset.univ.filter ((nnGraph d m).Adj x)).card : ℝ) ≤ 2 * d := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin d × Bool)))
      (f := fun p : Fin d × Bool => if p.2 then x + OAI.Anderson.torusBasisVector p.1
        else x - OAI.Anderson.torusBasisVector p.1)
    have h3 : (Finset.univ : Finset (Fin d × Bool)).card = 2 * d := by
      simp [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, mul_comm]
    exact_mod_cast (h1.trans h2).trans h3.le
  calc (∑ y, if (nnGraph d m).Adj x y then c else 0)
      = ((Finset.univ.filter ((nnGraph d m).Adj x)).card : ℝ) * c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * c := mul_le_mul_of_nonneg_right hcard hc

theorem setEnergy_congr (A : Finset (Torus d m)) (v w : Torus d m → ℝ) (a : ℝ)
    (h : ∀ x ∈ A, v x = w x + a) : setEnergy A v = setEnergy A w := by
  classical
  unfold setEnergy
  congr 1
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [h x hx, h y hy]
  split_ifs <;> ring

theorem constantKernel_setEdge (A : Finset (Torus d m)) (Pc : ℝ)
    (hP : ∀ v : Torus d m → ℝ, ∑ x ∈ A, (v x - setAvg A v) ^ 2 ≤ Pc * setEnergy A v) :
    S45.constantKernel (S45.laplacian (setEdge A)) := by
  classical
  refine ⟨AgentS45.laplacian_isSymm _ (setEdge_isSymm A), fun f => ?_,
    fun f => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [qform_setEdge]; exact setEnergy_nonneg _ _
  · rw [qform_setEdge] at h
    have hp := hP (extendSet A f)
    rw [h, mul_zero] at hp
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).1
      (le_antisymm hp (Finset.sum_nonneg fun x _ => sq_nonneg _))
    refine ⟨setAvg A (extendSet A f), fun i => ?_⟩
    have hi := hz i.1 i.2
    have hx : extendSet A f i.1 = f i := by simp [extendSet, i.2]
    rw [hx] at hi
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
    linarith
  · obtain ⟨a, ha⟩ := h
    rw [qform_setEdge]
    have : setEnergy A (extendSet A f) = setEnergy A (fun _ => 0) :=
      setEnergy_congr A _ _ a fun x hx => by simp [extendSet, hx, ha]
    rw [this]
    unfold setEnergy
    simp

/-- The energy of a cutoff product (05:285–291, product rule). -/
theorem energy_cutoff_le (A : Finset (Torus d m)) (χ g : Torus d m → ℝ) (ℓ : ℝ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (hz : ∀ x, x ∉ A → χ x = 0)
    (hlip : ∀ x y, (nnGraph d m).Adj x y → |χ x - χ y| ≤ ℓ) :
    torusEnergy d m (fun x => χ x * g x) ≤
      2 * setEnergy A g + 4 * d * ℓ ^ 2 * ∑ x ∈ A, g x ^ 2 := by
  classical
  have hpt : ∀ x y, (if (nnGraph d m).Adj x y then (χ x * g x - χ y * g y) ^ 2 else 0) ≤
      2 * (if x ∈ A then (if y ∈ A then (if (nnGraph d m).Adj x y then (g x - g y) ^ 2 else 0)
        else 0) else 0) +
      2 * ℓ ^ 2 * ((if (nnGraph d m).Adj x y then (if x ∈ A then g x ^ 2 else 0) else 0) +
        (if (nnGraph d m).Adj y x then (if y ∈ A then g y ^ 2 else 0) else 0)) := by
    intro x y
    by_cases hadj : (nnGraph d m).Adj x y
    · have hadj' : (nnGraph d m).Adj y x := hadj.symm
      have hl : (χ x - χ y) ^ 2 ≤ ℓ ^ 2 := by
        have := hlip x y hadj
        have h2 : |χ x - χ y| ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        simpa [sq_abs] using h2
      have hχx : χ x ^ 2 ≤ 1 := by nlinarith [h0 x, h1 x]
      have hgx := sq_nonneg (g x)
      have hgy := sq_nonneg (g y)
      have hℓ := sq_nonneg ℓ
      simp only [hadj, hadj', ite_true]
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp only [hx, hy, ite_true, ite_false]
      · have e1 : (χ x * g x - χ y * g y) ^ 2 ≤
            2 * (χ x ^ 2 * (g x - g y) ^ 2) + 2 * (g y ^ 2 * (χ x - χ y) ^ 2) := by
          nlinarith [sq_nonneg (χ x * (g x - g y) - g y * (χ x - χ y))]
        have e2 : χ x ^ 2 * (g x - g y) ^ 2 ≤ (g x - g y) ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) hχx
        have e3 : g y ^ 2 * (χ x - χ y) ^ 2 ≤ g y ^ 2 * ℓ ^ 2 :=
          mul_le_mul_of_nonneg_left hl hgy
        nlinarith [mul_nonneg hℓ hgx]
      · rw [hz y hy]
        have : (χ x * g x - 0 * g y) ^ 2 = g x ^ 2 * (χ x - 0) ^ 2 := by ring
        rw [this]
        have hl' : (χ x - 0) ^ 2 ≤ ℓ ^ 2 := by rw [← hz y hy]; exact hl
        nlinarith [mul_le_mul_of_nonneg_left hl' hgx]
      · rw [hz x hx]
        have : (0 * g x - χ y * g y) ^ 2 = g y ^ 2 * (0 - χ y) ^ 2 := by ring
        rw [this]
        have hl' : (0 - χ y) ^ 2 ≤ ℓ ^ 2 := by rw [← hz x hx]; exact hl
        nlinarith [mul_le_mul_of_nonneg_left hl' hgy]
      · rw [hz x hx, hz y hy]; simp
    · have hadj' : ¬ (nnGraph d m).Adj y x := fun h => hadj h.symm
      simp only [hadj, hadj', ite_false]
      simp
  have hdeg : ∀ x, (∑ y, if (nnGraph d m).Adj x y then (if x ∈ A then g x ^ 2 else 0) else 0) ≤
      2 * d * (if x ∈ A then g x ^ 2 else 0) := fun x =>
    sum_adj_le x _ (by split_ifs <;> positivity)
  have hsplit : torusEnergy d m (fun x => χ x * g x) ≤ (1 / 2) * ∑ x, ∑ y,
      (2 * (if x ∈ A then (if y ∈ A then (if (nnGraph d m).Adj x y then (g x - g y) ^ 2 else 0)
        else 0) else 0) +
      2 * ℓ ^ 2 * ((if (nnGraph d m).Adj x y then (if x ∈ A then g x ^ 2 else 0) else 0) +
        (if (nnGraph d m).Adj y x then (if y ∈ A then g y ^ 2 else 0) else 0))) := by
    unfold torusEnergy gradientEnergy
    gcongr with x _ y _
    convert hpt x y
  refine hsplit.trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  have hA : (∑ x, ∑ y, (if x ∈ A then (if y ∈ A then (if (nnGraph d m).Adj x y then
      (g x - g y) ^ 2 else 0) else 0) else 0)) = 2 * setEnergy A g := by
    have e1 : ∀ x, (∑ y, (if x ∈ A then (if y ∈ A then (if (nnGraph d m).Adj x y then
        (g x - g y) ^ 2 else 0) else 0) else 0)) = if x ∈ A then ∑ y ∈ A,
          (if (nnGraph d m).Adj x y then (g x - g y) ^ 2 else 0) else 0 := by
      intro x
      by_cases hx : x ∈ A
      · simp only [hx, ite_true]; rw [Finset.sum_ite_mem, Finset.univ_inter]
      · simp [hx]
    rw [Finset.sum_congr rfl fun x _ => e1 x, Finset.sum_ite_mem, Finset.univ_inter]
    unfold setEnergy
    ring
  have hB : (∑ x, ∑ y, (if (nnGraph d m).Adj x y then (if x ∈ A then g x ^ 2 else 0) else 0)) ≤
      2 * d * ∑ x ∈ A, g x ^ 2 := by
    calc _ ≤ ∑ x, 2 * d * (if x ∈ A then g x ^ 2 else 0) := Finset.sum_le_sum fun x _ => hdeg x
      _ = 2 * d * ∑ x ∈ A, g x ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  have hB' : (∑ x, ∑ y, (if (nnGraph d m).Adj y x then (if y ∈ A then g y ^ 2 else 0) else 0)) ≤
      2 * d * ∑ x ∈ A, g x ^ 2 := by
    rw [Finset.sum_comm]; exact hB
  have hs := setEnergy_nonneg A g
  have hl2 := sq_nonneg ℓ
  nlinarith [mul_le_mul_of_nonneg_left hB hl2, mul_le_mul_of_nonneg_left hB' hl2]


theorem torusEnergy_nonneg (v : Torus d m → ℝ) : 0 ≤ torusEnergy d m v := by
  classical
  unfold torusEnergy gradientEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  split_ifs <;> positivity

/-! ## Sums over the tiles -/

theorem sum_tiles_le {κ : Type} [Fintype κ] {ι' : Type} [Fintype ι'] (O : κ → ι' → Prop)
    [∀ T x, Decidable (O T x)] (A : ℝ)
    (hA : ∀ x, ((Finset.univ.filter fun T => O T x).card : ℝ) ≤ A)
    (F : ι' → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ T, ∑ x, (if O T x then F x else 0) ≤ A * ∑ x, F x := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (hF x)

/-! ## The restricted cover -/

theorem TilingAxioms.exists_cover {τ : TorusTiling d m} {t A B ℓ Pc C Cs Ck : ℝ}
    (hτ : TilingAxioms τ t A B ℓ Pc)
    (hconn : (nnGraph d m).Connected)
    (hshell : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d m,
      (∑ y, Real.exp (-u * physicalDistance d m x y)) ≤ Cs * S45.power u (-(d : ℝ)))
    (hker : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ v : Torus d m → ℝ,
      (∑ x, ∑ y, Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2) ≤
        Ck * S45.power u (-(d : ℝ) - 2) * torusEnergy d m v)
    (hCA : A ≤ C) (hCsplit : 2 + 4 * d * A ≤ C)
    (hCdim : 3 * B ≤ C * S45.power t (-6 * (d : ℝ)))
    (hCker : 8 * Cs + 4 * Ck ≤ C) (hCs0 : 0 ≤ Cs) (hCk0 : 0 ≤ Ck)
    {P : Type} [Fintype P] [DecidableEq P] (ι : P → Port d m) (hι : Function.Injective ι)
    (b : ℝ) (hb : 0 < b) :
    ∃ cov : S45.TileCover (P := P) (I := Torus d m) d t b C (pullDist ι),
      cov.site = (fun x => (ι x).1) ∧ cov.energy = torusEnergy d m ∧
      ∃ e : Fin cov.count ≃ Fin τ.count,
        (∀ T x, x ∈ cov.tile T ↔ (ι x).1 ∈ τ.tile (e T)) ∧
        (∀ T x, x ∈ cov.inner T ↔ (ι x).1 ∈ τ.inner (e T)) ∧
        (∀ T, ((cov.inner T).card : ℝ) ≤ 2 * B) := by
  classical
  let s : P → Torus d m := fun x => (ι x).1
  let cube : Fin τ.count → S45.LocalCube P (Torus d m) := fun T =>
    { site := s, outer := τ.outer T, cutoff := τ.cutoff T, edge := setEdge (τ.outer T) }
  have hports : ∀ T x, x ∈ (cube T).ports ↔ s x ∈ τ.outer T := fun T x => by
    simp [S45.LocalCube.ports, cube]
  have hkern : ∀ T, S45.constantKernel (S45.laplacian (cube T).edge) := fun T =>
    constantKernel_setEdge _ Pc (hτ.poincare T)
  let coords : ∀ T, S45.LocalCoordinates (cube T) b
      ((cube T).ports.card + (cube T).outer.card - 1) := fun T =>
    Classical.choice (AgentS45.local_coordinates_exist_proof (cube T) b hb
      (hτ.outer_nonempty T) (hkern T))
  have hA0 : 0 ≤ A := le_trans (by positivity) (hτ.overlap 0)
  obtain ⟨T₀, -, -⟩ := hτ.partition 0
  have hB0 : 0 ≤ B := le_trans (by positivity) (hτ.outer_card T₀)
  have hportcard : ∀ T, ((cube T).ports.card : ℝ) ≤ 2 * B := fun T => by
    have h := card_filter_port_le ι hι (τ.outer T)
    have : (cube T).ports = Finset.univ.filter fun x : P => (ι x).1 ∈ τ.outer T := by
      ext x; simp [hports, s]
    rw [this]; linarith [hτ.outer_card T]
  refine ⟨
    { site := s
      energy := torusEnergy d m
      count := τ.count
      tile := fun T => Finset.univ.filter fun x => s x ∈ τ.tile T
      inner := fun T => Finset.univ.filter fun x => s x ∈ τ.inner T
      cube := cube
      dim := fun T => (cube T).ports.card + (cube T).outer.card - 1
      coords := coords
      edge_symm := fun T => setEdge_isSymm _
      cutoff_one := ?_
      same_site := fun T => rfl
      cover := ?_
      inside := ?_
      buffer := ?_
      overlap := ?_
      dimension := ?_
      local_split := ?_
      kernel_energy := ?_
      local_sum := ?_ }, rfl, rfl, Equiv.refl _, ?_, ?_, ?_⟩
  · -- cutoff_one
    intro T i hi
    exact hτ.cutoff_one T _ (Finset.mem_filter.mp hi).2
  · -- cover
    intro x
    obtain ⟨T, hT, huniq⟩ := hτ.partition (s x)
    exact ⟨T, by simpa using hT, fun T' h => huniq T' (by simpa using h)⟩
  · -- inside
    intro T
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hτ.tile_inner T hx
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact (hports T x).2 (hτ.inner_outer T hx)
  · -- buffer
    intro T x hx i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hi
    exact hτ.buffer T (s x) hx (s i) hi
  · -- overlap
    intro i
    have h1 : (Finset.univ.filter fun T : Fin τ.count =>
        i ∈ Finset.univ.filter fun x => s x ∈ τ.inner T) ⊆
        Finset.univ.filter fun T => s i ∈ τ.outer T := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hτ.inner_outer T hT
    have h2 := Finset.card_le_card h1
    calc _ ≤ ((Finset.univ.filter fun T => s i ∈ τ.outer T).card : ℝ) := by exact_mod_cast h2
      _ ≤ A := hτ.overlap _
      _ ≤ C := hCA
  · -- dimension
    intro T
    have h1 : (((cube T).ports.card + (cube T).outer.card - 1 : ℕ) : ℝ) ≤
        (cube T).ports.card + (cube T).outer.card := by
      exact_mod_cast Nat.sub_le _ _
    have h2 : ((cube T).outer.card : ℝ) ≤ B := hτ.outer_card T
    linarith [hportcard T]
  · -- local_split
    intro T w
    let Q := cube T
    let a := coords T
    let α₀ : Q.ports → ℝ := fun i => (a.alpha *ᵥ w) i
    let v₀ : Q.outer → ℝ := fun i => (a.potential *ᵥ w) i
    let mean : ℝ := (∑ i, v₀ i) / Q.outer.card
    let g : Torus d m → ℝ := fun i => extendSet (τ.outer T) v₀ i - mean
    let α' : P → ℝ := fun x => if hx : x ∈ Q.ports then τ.cutoff T (s x) * α₀ ⟨x, hx⟩ else 0
    let v' : Torus d m → ℝ := fun i => τ.cutoff T i * g i
    refine ⟨α', v', fun x => ?_, ?_⟩
    · show (a.B *ᵥ w) x = α' x + v' (s x)
      rw [AgentS45.local_coordinates_B_mulVec Q b _ a w]
      unfold S45.LocalCube.extend
      by_cases hx : x ∈ Q.ports
      · have hsx : s x ∈ τ.outer T := (hports T x).1 hx
        have hg : g (s x) = v₀ ⟨s x, hsx⟩ - mean := by simp [g, extendSet, hsx]
        simp only [α', v', dif_pos hx, hg]
        show τ.cutoff T (s x) * (α₀ ⟨x, hx⟩ + v₀ ⟨s x, _⟩ - (∑ i, v₀ i) / Q.outer.card) = _
        simp only [mean]
        ring
      · have hsx : s x ∉ τ.outer T := fun h => hx ((hports T x).2 h)
        simp only [α', v', dif_neg hx, hτ.cutoff_zero T _ hsx]
        ring
    · show S45.l2sq α' + torusEnergy d m v' / b ≤ C * S45.l2sq w
      have hnorm : S45.l2sq α₀ + S45.qform (S45.laplacian Q.edge) v₀ / b = S45.l2sq w :=
        a.normalized w
      have hqf : S45.qform (S45.laplacian Q.edge) v₀ =
          setEnergy (τ.outer T) (extendSet (τ.outer T) v₀) := qform_setEdge _ v₀
      set qf := S45.qform (S45.laplacian Q.edge) v₀ with hqf_def
      have hqf0 : 0 ≤ qf := hqf ▸ setEnergy_nonneg _ _
      have hα0 : 0 ≤ S45.l2sq α₀ := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hw0 : 0 ≤ S45.l2sq w := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hα : S45.l2sq α' ≤ S45.l2sq α₀ := by
        unfold S45.l2sq
        rw [← Finset.sum_subset (Finset.subset_univ Q.ports)
          (fun x _ hx => by simp [α', hx])]
        rw [← Finset.sum_coe_sort Q.ports]
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : α' i.1 = τ.cutoff T (s i.1) * α₀ i := by simp [α', i.2]
        rw [hi, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _)
          (by nlinarith [hτ.cutoff_nonneg T (s i.1), hτ.cutoff_le_one T (s i.1)])
      have hE := energy_cutoff_le (τ.outer T) (τ.cutoff T) g ℓ (hτ.cutoff_nonneg T)
        (hτ.cutoff_le_one T) (hτ.cutoff_zero T) (hτ.lip T)
      have hgE : setEnergy (τ.outer T) g = qf := by
        rw [hqf]
        exact setEnergy_congr _ _ _ (-mean) (fun x _ => by simp only [g]; ring)
      have hgP : ∑ x ∈ τ.outer T, g x ^ 2 ≤ Pc * qf := by
        have hp := hτ.poincare T (extendSet (τ.outer T) v₀)
        have havg : setAvg (τ.outer T) (extendSet (τ.outer T) v₀) = mean := by
          unfold setAvg
          simp only [mean]
          congr 1
          rw [← Finset.sum_coe_sort (τ.outer T)]
          exact Finset.sum_congr rfl fun i _ => by simp [extendSet, i.2]
        rw [havg, ← hqf] at hp
        exact hp
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hl : 4 * d * ℓ ^ 2 * (∑ x ∈ τ.outer T, g x ^ 2) ≤ 4 * d * A * qf := by
        have h1 : ℓ ^ 2 * (∑ x ∈ τ.outer T, g x ^ 2) ≤ ℓ ^ 2 * (Pc * qf) :=
          mul_le_mul_of_nonneg_left hgP (sq_nonneg _)
        have h2 : ℓ ^ 2 * (Pc * qf) ≤ A * qf := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hτ.lip_pc hqf0
        nlinarith
      have hEn : torusEnergy d m v' ≤ (2 + 4 * d * A) * qf := by
        have : torusEnergy d m v' = torusEnergy d m (fun x => τ.cutoff T x * g x) := rfl
        rw [this]; nlinarith
      have hK : (1 : ℝ) ≤ 2 + 4 * d * A := by nlinarith
      calc S45.l2sq α' + torusEnergy d m v' / b
          ≤ S45.l2sq α₀ + (2 + 4 * d * A) * qf / b :=
            add_le_add hα (div_le_div_of_nonneg_right hEn hb.le)
        _ ≤ (2 + 4 * d * A) * (S45.l2sq α₀ + qf / b) := by
            have : 0 ≤ qf / b := div_nonneg hqf0 hb.le
            rw [mul_add, mul_div_assoc]
            nlinarith
        _ = (2 + 4 * d * A) * S45.l2sq w := by rw [hnorm]
        _ ≤ C * S45.l2sq w := mul_le_mul_of_nonneg_right hCsplit hw0
  · -- kernel_energy
    intro u hu0 hu1 α v
    show (1 / 2 : ℝ) * ∑ i, ∑ j, Real.exp (-u * pullDist ι i j) *
        (α i + v (s i) - α j - v (s j)) ^ 2 ≤
      C * (S45.power u (-(d : ℝ)) * S45.l2sq α + S45.power u (-(d : ℝ) - 2) * torusEnergy d m v)
    set pw := S45.power u (-(d : ℝ)) with hpw
    set pw2 := S45.power u (-(d : ℝ) - 2) with hpw2
    have hpw0 : 0 ≤ pw := Real.rpow_nonneg hu0.le _
    have hpw20 : 0 ≤ pw2 := Real.rpow_nonneg hu0.le _
    let E : P → P → ℝ := fun i j => Real.exp (-u * pullDist ι i j)
    have hE0 : ∀ i j, 0 ≤ E i j := fun i j => (Real.exp_pos _).le
    have hEs : ∀ i j, E i j = E j i := fun i j => by
      simp only [E, pullDist, physicalDistance, SimpleGraph.dist_comm]
    have hrow : ∀ i, ∑ j, E i j ≤ 2 * Cs * pw := fun i => by
      have h1 := sum_port_le ι hι (fun y => Real.exp (-u * physicalDistance d m (s i) y))
        (fun y => (Real.exp_pos _).le)
      have h2 := hshell u hu0 hu1 (s i)
      calc ∑ j, E i j = ∑ j, Real.exp (-u * physicalDistance d m (s i) (ι j).1) := rfl
        _ ≤ 2 * ∑ y, Real.exp (-u * physicalDistance d m (s i) y) := h1
        _ ≤ 2 * (Cs * pw) := by linarith
        _ = 2 * Cs * pw := by ring
    have hcol : ∀ j, ∑ i, E i j ≤ 2 * Cs * pw := fun j => by
      rw [Finset.sum_congr rfl fun i _ => hEs i j]; exact hrow j
    have hpt : ∀ i j, E i j * (α i + v (s i) - α j - v (s j)) ^ 2 ≤
        4 * (E i j * α i ^ 2) + 4 * (E i j * α j ^ 2) +
          2 * (Real.exp (-u * physicalDistance d m (ι i).1 (ι j).1) *
            (v (ι i).1 - v (ι j).1) ^ 2) := by
      intro i j
      have h : (α i + v (s i) - α j - v (s j)) ^ 2 ≤
          4 * α i ^ 2 + 4 * α j ^ 2 + 2 * (v (s i) - v (s j)) ^ 2 := by
        nlinarith [sq_nonneg (α i + α j), sq_nonneg (α i - α j - (v (s i) - v (s j)))]
      calc _ ≤ E i j * (4 * α i ^ 2 + 4 * α j ^ 2 + 2 * (v (s i) - v (s j)) ^ 2) :=
            mul_le_mul_of_nonneg_left h (hE0 i j)
        _ = _ := by simp only [E, pullDist, s]; ring
    have hl2 : S45.l2sq α = ∑ i, α i ^ 2 := by
      unfold S45.l2sq; simp [Real.norm_eq_abs, sq_abs]
    have hX1 : ∑ i, ∑ j, E i j * α i ^ 2 ≤ 2 * Cs * pw * S45.l2sq α := by
      rw [hl2, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    have hX2 : ∑ i, ∑ j, E i j * α j ^ 2 ≤ 2 * Cs * pw * S45.l2sq α := by
      rw [Finset.sum_comm, hl2, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    have hX3 : ∑ i, ∑ j, Real.exp (-u * physicalDistance d m (ι i).1 (ι j).1) *
        (v (ι i).1 - v (ι j).1) ^ 2 ≤ 4 * (Ck * pw2 * torusEnergy d m v) := by
      have h := sum_port_pair_le ι hι
        (fun x y => Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2)
        (fun x y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      have h2 := hker u hu0 hu1 v
      calc _ ≤ _ := h
        _ ≤ 4 * (Ck * pw2 * torusEnergy d m v) := by linarith
    have hsum : ∑ i, ∑ j, E i j * (α i + v (s i) - α j - v (s j)) ^ 2 ≤
        4 * (∑ i, ∑ j, E i j * α i ^ 2) + 4 * (∑ i, ∑ j, E i j * α j ^ 2) +
          2 * (∑ i, ∑ j, Real.exp (-u * physicalDistance d m (ι i).1 (ι j).1) *
            (v (ι i).1 - v (ι j).1) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    have hL0 : 0 ≤ S45.l2sq α := by rw [hl2]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hΛ0 := torusEnergy_nonneg (d := d) (m := m) v
    have hc1 : 8 * Cs * (pw * S45.l2sq α) ≤ C * (pw * S45.l2sq α) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hpw0 hL0)
    have hc2 : 4 * Ck * (pw2 * torusEnergy d m v) ≤ C * (pw2 * torusEnergy d m v) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hpw20 hΛ0)
    show (1 / 2 : ℝ) * ∑ i, ∑ j, E i j * (α i + v (s i) - α j - v (s j)) ^ 2 ≤ _
    nlinarith
  · -- local_sum
    intro α v
    show ∑ T, (cube T).energy b (fun x => α x) (fun i => v i) ≤
      C * (S45.l2sq α + torusEnergy d m v / b)
    have hT : ∀ T, (cube T).energy b (fun x => α x) (fun i => v i) =
        (∑ x, if s x ∈ τ.outer T then α x ^ 2 else 0) + setEnergy (τ.outer T) v / b := by
      intro T
      unfold S45.LocalCube.energy
      congr 1
      · unfold S45.l2sq
        rw [Finset.sum_coe_sort (cube T).ports (fun x => ‖α x‖ ^ 2)]
        rw [show (cube T).ports = Finset.univ.filter fun x => s x ∈ τ.outer T from rfl,
          Finset.sum_filter]
        simp [Real.norm_eq_abs, sq_abs]
      · rw [qform_setEdge]
        congr 1
        exact setEnergy_congr _ _ _ 0 (fun x hx => by simp [extendSet, hx])
    rw [Finset.sum_congr rfl fun T _ => hT T, Finset.sum_add_distrib, ← Finset.sum_div]
    have hl2 : S45.l2sq α = ∑ i, α i ^ 2 := by
      unfold S45.l2sq; simp [Real.norm_eq_abs, sq_abs]
    have h1 : ∑ T, ∑ x, (if s x ∈ τ.outer T then α x ^ 2 else 0) ≤ A * S45.l2sq α := by
      rw [hl2]
      exact sum_tiles_le (fun T x => s x ∈ τ.outer T) A (fun x => hτ.overlap (s x)) _
        (fun x => sq_nonneg _)
    have h2 : ∑ T, setEnergy (τ.outer T) v ≤ A * torusEnergy d m v := by
      let F : Torus d m → ℝ := fun x => ∑ y, if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0
      have hF0 : ∀ x, 0 ≤ F x := fun x => Finset.sum_nonneg fun y _ => by
        split_ifs <;> positivity
      have hle : ∀ T, setEnergy (τ.outer T) v ≤
          (1 / 2) * ∑ x, if x ∈ τ.outer T then F x else 0 := fun T => by
        unfold setEnergy
        rw [Finset.sum_ite_mem, Finset.univ_inter]
        gcongr with x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun y _ _ => by split_ifs <;> positivity)
      calc ∑ T, setEnergy (τ.outer T) v
          ≤ ∑ T, (1 / 2) * ∑ x, (if x ∈ τ.outer T then F x else 0) :=
            Finset.sum_le_sum fun T _ => hle T
        _ = (1 / 2) * ∑ T, ∑ x, (if x ∈ τ.outer T then F x else 0) := by rw [Finset.mul_sum]
        _ ≤ (1 / 2) * (A * ∑ x, F x) := by
            gcongr
            exact sum_tiles_le (fun T x => x ∈ τ.outer T) A hτ.overlap F hF0
        _ = A * torusEnergy d m v := by
            unfold torusEnergy gradientEnergy; simp only [F]; ring
    have hL0 : 0 ≤ S45.l2sq α := by rw [hl2]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hΛ0 := torusEnergy_nonneg (d := d) (m := m) v
    have h2' : (∑ T, setEnergy (τ.outer T) v) / b ≤ A * (torusEnergy d m v / b) := by
      rw [mul_div_assoc']; exact div_le_div_of_nonneg_right h2 hb.le
    have hc : A * (S45.l2sq α + torusEnergy d m v / b) ≤ C * (S45.l2sq α + torusEnergy d m v / b) :=
      mul_le_mul_of_nonneg_right hCA (add_nonneg hL0 (div_nonneg hΛ0 hb.le))
    nlinarith
  · intro T x; simp [s]
  · intro T x; simp [s]
  · intro T
    have h := card_filter_port_le ι hι (τ.inner T)
    have h2 : ((τ.inner T).card : ℝ) ≤ B := by
      have := Finset.card_le_card (hτ.inner_outer T)
      have h3 : ((τ.inner T).card : ℝ) ≤ (τ.outer T).card := by exact_mod_cast this
      linarith [hτ.outer_card T]
    simp only [s] at *
    linarith

end AndersonAC.AgentS78
