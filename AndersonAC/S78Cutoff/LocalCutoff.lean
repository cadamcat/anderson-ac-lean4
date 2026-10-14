import AndersonAC.S3WCube.Weighted
import AndersonAC.S78Local.WeightedLocalEnergy
import AndersonAC.S78.AssemblyEstimates

/-! Proof of the frozen `AndersonAC.SolS78.LocalCutoffInput`.

Route: on the embedded enlarged cube `Q = cube z (2R)` subtract a mean `μ`
for which the cube Poincare inequality holds (transported from the proved
§3 `weighted_cube` through `SolS78Local.localCubeEquiv`); multiply by a
product cutoff `χ` that is `1` on the `R`-cube, vanishes (with a one-site
buffer) outside `Q`, and changes by at most `1 / D` along an edge, where
`D = ⌊2R⌋ - ⌊R⌋ ≥ R / 2`. The decomposition `F = χ α + χ (v - μ)` gives the
bound. Does not import `S78.Statements`. -/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Cutoff

open AndersonAC.S78 AndersonAC.SolS78Local

variable {d m : ℕ}

/-! ### Coordinate distances -/

lemma mem_cube_iff (z x : Torus d m) (s : ℝ) :
    x ∈ cube d m z s ↔ ∀ i, (((x i - z i).valMinAbs.natAbs : ℕ) : ℝ) ≤ s := by
  classical
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and,
    ZMod.valMinAbs_natAbs_eq_min]

lemma natAbs_valMinAbs_one_le {n : ℕ} [NeZero n] :
    (1 : ZMod n).valMinAbs.natAbs ≤ 1 := by
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_one_eq_one_mod]
  exact (min_le_left _ _).trans (Nat.mod_le _ _)

lemma natAbs_add_unit_le {n : ℕ} [NeZero n] (a s : ZMod n) (hs : s = 1 ∨ s = -1) :
    (a + s).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + 1 := by
  have h1 : s.valMinAbs.natAbs ≤ 1 := by
    rcases hs with rfl | rfl
    · exact natAbs_valMinAbs_one_le
    · rw [ZMod.natAbs_valMinAbs_neg]
      exact natAbs_valMinAbs_one_le
  calc (a + s).valMinAbs.natAbs ≤ (a.valMinAbs + s.valMinAbs).natAbs :=
        ZMod.natAbs_valMinAbs_add_le a s
    _ ≤ a.valMinAbs.natAbs + s.valMinAbs.natAbs := Int.natAbs_add_le _ _
    _ ≤ a.valMinAbs.natAbs + 1 := by omega

lemma adj_coords (x y : Torus d m) (h : (nnGraph d m).Adj x y) :
    ∃ k : Fin d, (∀ j, j ≠ k → y j = x j) ∧
      ∃ s : ZMod (OAI.Anderson.sideLength m), (s = 1 ∨ s = -1) ∧ y k = x k + s := by
  rw [nnGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h⟩ := h
  rcases h with ⟨k, hk | hk⟩ | ⟨k, hk | hk⟩
  · refine ⟨k, fun j hj => ?_, 1, Or.inl rfl, ?_⟩
    · rw [hk]; simp [OAI.Anderson.torusBasisVector, hj]
    · rw [hk]; simp [OAI.Anderson.torusBasisVector]
  · refine ⟨k, fun j hj => ?_, -1, Or.inr rfl, ?_⟩
    · rw [hk]; simp [OAI.Anderson.torusBasisVector, hj]
    · rw [hk]; simp [OAI.Anderson.torusBasisVector, sub_eq_add_neg]
  · refine ⟨k, fun j hj => ?_, -1, Or.inr rfl, ?_⟩
    · rw [hk]; simp [OAI.Anderson.torusBasisVector, hj]
    · rw [hk]; simp [OAI.Anderson.torusBasisVector]
  · refine ⟨k, fun j hj => ?_, 1, Or.inl rfl, ?_⟩
    · rw [hk]; simp [OAI.Anderson.torusBasisVector, hj]
    · rw [hk]; simp [OAI.Anderson.torusBasisVector]

lemma adj_dist_le (z x y : Torus d m) (h : (nnGraph d m).Adj x y) (i : Fin d) :
    (y i - z i).valMinAbs.natAbs ≤ (x i - z i).valMinAbs.natAbs + 1 := by
  obtain ⟨k, hother, s, hs, hk⟩ := adj_coords x y h
  by_cases hik : i = k
  · subst hik
    have : y i - z i = (x i - z i) + s := by rw [hk]; ring
    rw [this]
    exact natAbs_add_unit_le _ _ hs
  · rw [hother i hik]
    omega

lemma card_adj_le (Q : Finset (Torus d m)) (y : Torus d m)
    [DecidablePred fun x => (nnGraph d m).Adj x y] :
    (Q.filter (fun x => (nnGraph d m).Adj x y)).card ≤ 2 * d := by
  classical
  have hsub : Q.filter (fun x => (nnGraph d m).Adj x y) ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        (fun p => y + Pi.single p.1
          (if p.2 then (1 : ZMod (OAI.Anderson.sideLength m)) else -1)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨k, hother, s, hs, hk⟩ := adj_coords y x hx.2.symm
    rw [Finset.mem_image]
    refine ⟨(k, decide (s = 1)), Finset.mem_univ _, ?_⟩
    have hsv : (if decide (s = 1) = true then (1 : ZMod (OAI.Anderson.sideLength m))
        else -1) = s := by
      by_cases h1 : s = 1
      · simp [h1]
      · rcases hs with h | h
        · exact absurd h h1
        · rw [if_neg (by simpa using h1)]
          exact h.symm
    funext j
    simp only [Pi.add_apply]
    rw [hsv]
    by_cases hj : j = k
    · subst hj
      simp [hk]
    · rw [Pi.single_eq_of_ne hj, hother j hj, add_zero]
  calc (Q.filter (fun x => (nnGraph d m).Adj x y)).card
      ≤ ((Finset.univ : Finset (Fin d × Bool)).image _).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, mul_comm]

/-! ### The cutoff profile -/

def phi (N D t : ℝ) : ℝ := max 0 (min 1 ((N - t) / D))

lemma phi_nonneg (N D t : ℝ) : 0 ≤ phi N D t := le_max_left _ _

lemma phi_le_one (N D t : ℝ) : phi N D t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma phi_eq_one {N D t : ℝ} (hD : 0 < D) (h : t + D ≤ N) : phi N D t = 1 := by
  have h1 : 1 ≤ (N - t) / D := by rw [le_div_iff₀ hD]; linarith
  rw [phi, min_eq_left h1, max_eq_right zero_le_one]

lemma phi_eq_zero {N D t : ℝ} (hD : 0 < D) (h : N ≤ t) : phi N D t = 0 := by
  have h0 : (N - t) / D ≤ 0 := by rw [div_le_iff₀ hD]; linarith
  rw [phi]
  exact max_eq_left ((min_le_right _ _).trans h0)

lemma phi_lip {N D : ℝ} (hD : 0 < D) (s t : ℝ) :
    |phi N D s - phi N D t| ≤ |s - t| / D := by
  unfold phi
  calc |max 0 (min 1 ((N - s) / D)) - max 0 (min 1 ((N - t) / D))|
      = |max (min 1 ((N - s) / D)) 0 - max (min 1 ((N - t) / D)) 0| := by
        rw [max_comm 0, max_comm 0]
    _ ≤ |min 1 ((N - s) / D) - min 1 ((N - t) / D)| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |(N - s) / D - (N - t) / D| := abs_min_sub_min_le_max _ _ _ _
    _ = |s - t| / D := by
        have : (N - s) / D - (N - t) / D = (t - s) / D := by ring
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), this, abs_div,
          abs_of_pos hD, abs_sub_comm]

def chi (z : Torus d m) (N D : ℝ) (x : Torus d m) : ℝ :=
  ∏ i, phi N D ((x i - z i).valMinAbs.natAbs : ℝ)

lemma chi_nonneg (z : Torus d m) (N D : ℝ) (x : Torus d m) : 0 ≤ chi z N D x :=
  Finset.prod_nonneg fun i _ => phi_nonneg _ _ _

lemma chi_le_one (z : Torus d m) (N D : ℝ) (x : Torus d m) : chi z N D x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => phi_nonneg _ _ _) (fun i _ => phi_le_one _ _ _)

lemma chi_eq_one (z : Torus d m) {N D : ℝ} (hD : 0 < D) (x : Torus d m)
    (h : ∀ i, ((x i - z i).valMinAbs.natAbs : ℝ) + D ≤ N) : chi z N D x = 1 :=
  Finset.prod_eq_one fun i _ => phi_eq_one hD (h i)

lemma lt_of_chi_ne_zero (z : Torus d m) {N D : ℝ} (hD : 0 < D) (x : Torus d m)
    (h : chi z N D x ≠ 0) (i : Fin d) : ((x i - z i).valMinAbs.natAbs : ℝ) < N := by
  by_contra hle
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (phi_eq_zero hD (le_of_not_gt hle))

lemma chi_lip (z : Torus d m) {N D : ℝ} (hD : 0 < D) (x y : Torus d m)
    (h : (nnGraph d m).Adj x y) : |chi z N D x - chi z N D y| ≤ 1 / D := by
  classical
  obtain ⟨k, hother, -, -, -⟩ := adj_coords x y h
  let f : Torus d m → Fin d → ℝ := fun p i => phi N D ((p i - z i).valMinAbs.natAbs : ℝ)
  have hx : chi z N D x = f x k * ∏ i ∈ Finset.univ.erase k, f x i :=
    (Finset.mul_prod_erase Finset.univ (f x) (Finset.mem_univ k)).symm
  have hy : chi z N D y = f y k * ∏ i ∈ Finset.univ.erase k, f y i :=
    (Finset.mul_prod_erase Finset.univ (f y) (Finset.mem_univ k)).symm
  have hP : ∏ i ∈ Finset.univ.erase k, f y i = ∏ i ∈ Finset.univ.erase k, f x i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f, hother i (Finset.ne_of_mem_erase hi)]
  set P := ∏ i ∈ Finset.univ.erase k, f x i
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => phi_nonneg _ _ _
  have hP1 : P ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => phi_nonneg _ _ _) (fun i _ => phi_le_one _ _ _)
  have hd1 := adj_dist_le z x y h k
  have hd2 := adj_dist_le z y x h.symm k
  have hdist : |(((x k - z k).valMinAbs.natAbs : ℕ) : ℝ) -
      (((y k - z k).valMinAbs.natAbs : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : (((y k - z k).valMinAbs.natAbs : ℕ) : ℝ) ≤
          (((x k - z k).valMinAbs.natAbs : ℕ) : ℝ) + 1 := by exact_mod_cast hd1
      linarith
    · have : (((x k - z k).valMinAbs.natAbs : ℕ) : ℝ) ≤
          (((y k - z k).valMinAbs.natAbs : ℕ) : ℝ) + 1 := by exact_mod_cast hd2
      linarith
  rw [hx, hy, hP, ← sub_mul, abs_mul, abs_of_nonneg hP0]
  calc |f x k - f y k| * P ≤ |f x k - f y k| * 1 :=
        mul_le_mul_of_nonneg_left hP1 (abs_nonneg _)
    _ = |f x k - f y k| := mul_one _
    _ ≤ |(((x k - z k).valMinAbs.natAbs : ℕ) : ℝ) -
          (((y k - z k).valMinAbs.natAbs : ℕ) : ℝ)| / D := phi_lip hD _ _
    _ ≤ 1 / D := div_le_div_of_nonneg_right hdist hD.le

/-! ### Energies -/

lemma gradientEnergy_nonneg' {ι : Type} [Fintype ι] (G : SimpleGraph ι) (f : ι → ℝ) :
    0 ≤ gradientEnergy G f := by
  classical
  unfold gradientEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma cubeGradient_nonneg' (Q : Finset (Torus d m)) (v : Torus d m → ℝ) :
    0 ≤ cubeGradient d m Q v := by
  classical
  unfold cubeGradient
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- Gradient energy of a cutoff product, controlled on the enlarged cube. -/
lemma grad_cutoff_le (Q : Finset (Torus d m)) (χ w v u : Torus d m → ℝ) (D : ℝ)
    (hu : ∀ x, u x = χ x * w x)
    (hw : ∀ x y, w x - w y = v x - v y)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hlip : ∀ x y, (nnGraph d m).Adj x y → |χ x - χ y| ≤ 1 / D)
    (hsupp : ∀ x y, (nnGraph d m).Adj x y → χ x ≠ 0 → x ∈ Q ∧ y ∈ Q) :
    gradientEnergy (nnGraph d m) u ≤
      2 * cubeGradient d m Q v + 2 * d * ∑ y ∈ Q, w y ^ 2 / D ^ 2 := by
  classical
  set G := nnGraph d m with hG
  -- pointwise bound on an adjacent pair inside `Q`
  have hpt : ∀ x y, G.Adj x y →
      (u x - u y) ^ 2 ≤ 2 * (v x - v y) ^ 2 + 2 * (w y ^ 2 / D ^ 2) := by
    intro x y hadj
    have hsplit : u x - u y = χ x * (v x - v y) + w y * (χ x - χ y) := by
      rw [hu, hu, ← hw x y]; ring
    have h1 : (χ x * (v x - v y)) ^ 2 ≤ (v x - v y) ^ 2 := by
      rw [mul_pow]
      have : χ x ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
      nlinarith [sq_nonneg (v x - v y)]
    have h2 : (w y * (χ x - χ y)) ^ 2 ≤ w y ^ 2 / D ^ 2 := by
      have hsq : (χ x - χ y) ^ 2 ≤ (1 / D) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hlip x y hadj) 2
      rw [mul_pow]
      calc w y ^ 2 * (χ x - χ y) ^ 2 ≤ w y ^ 2 * (1 / D) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = w y ^ 2 / D ^ 2 := by rw [div_pow, one_pow, mul_one_div]
    rw [hsplit]
    nlinarith [sq_nonneg (χ x * (v x - v y) - w y * (χ x - χ y))]
  -- terms vanish off `Q × Q`
  have hzero : ∀ x y, (x ∉ Q ∨ y ∉ Q) →
      (if G.Adj x y then (u x - u y) ^ 2 else 0) = 0 := by
    intro x y hxy
    by_cases hadj : G.Adj x y
    · rw [if_pos hadj]
      have hx : χ x = 0 := by
        by_contra hx
        have := hsupp x y hadj hx
        rcases hxy with h | h
        · exact h this.1
        · exact h this.2
      have hy : χ y = 0 := by
        by_contra hy
        have := hsupp y x hadj.symm hy
        rcases hxy with h | h
        · exact h this.2
        · exact h this.1
      rw [hu, hu, hx, hy]
      ring
    · rw [if_neg hadj]
  have hrestrict : (∑ x, ∑ y, if G.Adj x y then (u x - u y) ^ 2 else 0) =
      ∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then (u x - u y) ^ 2 else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ Q)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_subset (Finset.subset_univ Q)]
      intro y _ hy
      exact hzero x y (Or.inr hy)
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro y _
      exact hzero x y (Or.inl hx)
  have hbound : (∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then (u x - u y) ^ 2 else 0) ≤
      ∑ x ∈ Q, ∑ y ∈ Q, (2 * (if G.Adj x y then (v x - v y) ^ 2 else 0) +
        2 * (if G.Adj x y then w y ^ 2 / D ^ 2 else 0)) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    by_cases hadj : G.Adj x y
    · rw [if_pos hadj, if_pos hadj, if_pos hadj]
      exact hpt x y hadj
    · rw [if_neg hadj, if_neg hadj, if_neg hadj]
      norm_num
  have hcg : cubeGradient d m Q v =
      (1 / 2) * ∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then (v x - v y) ^ 2 else 0 := by
    unfold cubeGradient
    congr 1
  have hdeg : (∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then w y ^ 2 / D ^ 2 else 0) ≤
      ∑ y ∈ Q, (2 * d : ℝ) * (w y ^ 2 / D ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast card_adj_le Q y
  have hge : gradientEnergy G u =
      (1 / 2) * ∑ x, ∑ y, if G.Adj x y then (u x - u y) ^ 2 else 0 := by
    unfold gradientEnergy
    congr 1
  rw [hge, hrestrict]
  have hsplit2 : (∑ x ∈ Q, ∑ y ∈ Q, (2 * (if G.Adj x y then (v x - v y) ^ 2 else 0) +
        2 * (if G.Adj x y then w y ^ 2 / D ^ 2 else 0))) =
      2 * (∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then (v x - v y) ^ 2 else 0) +
        2 * (∑ x ∈ Q, ∑ y ∈ Q, if G.Adj x y then w y ^ 2 / D ^ 2 else 0) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hdeg' : (∑ y ∈ Q, (2 * d : ℝ) * (w y ^ 2 / D ^ 2)) =
      2 * d * ∑ y ∈ Q, w y ^ 2 / D ^ 2 := by rw [Finset.mul_sum]
  rw [hsplit2] at hbound
  rw [hcg]
  linarith [hbound, hdeg, hdeg']

/-- Cube Poincare on the physical enlarged cube, from §3 `weighted_cube`. -/
lemma cube_poincare (hCube : S3WeightedCubeStatement d) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ (m : ℕ) (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
      (_hside : 4 * R < (OAI.Anderson.sideLength m : ℝ)) (v : Torus d m → ℝ),
      ∃ μ : ℝ, ∑ q ∈ cube d m z (2 * R), (v q - μ) ^ 2 ≤
        Cw * (localCubeLength R : ℝ) ^ 2 * cubeGradient d m (cube d m z (2 * R)) v := by
  obtain ⟨Cw, hCw, hCubeB⟩ := hCube
  refine ⟨Cw, hCw, ?_⟩
  intro m z R hR hside v
  classical
  let e := localCubeEquiv z R hR hside
  let T := localCubeToTorus (d := d) (m := m) z R
  let vC : CoordCube d (localCubeLength R) → ℂ := fun x => (v (T x) : ℂ)
  let μ : ℝ := ((Fintype.card (CoordCube d (localCubeLength R)) : ℝ))⁻¹ * ∑ x, v (T x)
  refine ⟨μ, ?_⟩
  have hlen : 1 ≤ localCubeLength R := by unfold localCubeLength; omega
  have hP := (hCubeB (localCubeLength R) hlen vC (fun _ => 0) (fun _ => le_rfl)).1
  have hmean : coordCubeMean vC = (μ : ℂ) := by
    simp only [coordCubeMean, vC, μ]
    push_cast
    rfl
  have hnorm : coordCubeNormSq (fun i => vC i - coordCubeMean vC) =
      ∑ x, (v (T x) - μ) ^ 2 := by
    unfold coordCubeNormSq
    rw [hmean]
    apply Finset.sum_congr rfl
    intro x _
    have hcast : ((v (T x) - μ : ℝ) : ℂ) = (v (T x) : ℂ) - (μ : ℂ) := by push_cast; rfl
    simp only [vC]
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have htrans : ∑ x, (v (T x) - μ) ^ 2 = ∑ q ∈ cube d m z (2 * R), (v q - μ) ^ 2 := by
    calc ∑ x, (v (T x) - μ) ^ 2
        = ∑ x, (fun q : localCubeDomain z R => (v q.val - μ) ^ 2) (e x) := rfl
      _ = ∑ q : localCubeDomain z R, (v q.val - μ) ^ 2 :=
          Equiv.sum_comp e (fun q : localCubeDomain z R => (v q.val - μ) ^ 2)
      _ = _ := localCubeDomain_sum z R (fun q => (v q - μ) ^ 2)
  have hE := coordCubeEnergy_le_cubeGradient z R hR hside v
  rw [hnorm, htrans] at hP
  calc _ ≤ _ := hP
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

end AndersonAC.AgentS78Cutoff

namespace AndersonAC.SolS78

open AndersonAC.S78 AndersonAC.SolS78Local AndersonAC.AgentS78Cutoff

theorem localCutoffInput_proof : LocalCutoffInput := by
  intro d hd
  obtain ⟨Cw, hCw, hPoin⟩ :=
    cube_poincare (d := d) (AndersonAC.AgentS3.weighted_cube_proof hd)
  refine ⟨2 + 200 * d * Cw, by positivity, ?_⟩
  intro m z R b A α v hR hside hb
  classical
  obtain ⟨μ, hμ⟩ := hPoin m z R hR hside v
  set Q := cube d m z (2 * R) with hQ
  have hR0 : 0 ≤ R := by linarith
  set n : ℕ := ⌊R⌋₊ with hn
  set N : ℕ := ⌊2 * R⌋₊ with hN
  have hn_le : (n : ℝ) ≤ R := Nat.floor_le hR0
  have hN_le : (N : ℝ) ≤ 2 * R := Nat.floor_le (by linarith)
  have hN_gt : 2 * R < N + 1 := Nat.lt_floor_add_one _
  have hnN : n + 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  set D : ℝ := (N : ℝ) - n with hD
  have hD1 : 1 ≤ D := by
    have : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hnN
    push_cast at this
    linarith
  have hD0 : 0 < D := by linarith
  have hDR : R ≤ 2 * D := by linarith
  have hlen : (localCubeLength R : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [hN]
    unfold localCubeLength localCubeRadius
    push_cast
    ring
  have hl2 : (localCubeLength R : ℝ) ^ 2 ≤ 100 * D ^ 2 := by
    have h0 : (0 : ℝ) ≤ localCubeLength R := Nat.cast_nonneg _
    have h1 : (localCubeLength R : ℝ) ≤ 10 * D := by rw [hlen]; linarith
    nlinarith
  let χ : Torus d m → ℝ := chi z (N : ℝ) D
  let w : Torus d m → ℝ := fun x => v x - μ
  let u : Torus d m → ℝ := fun x => χ x * w x
  let a : Torus d m → ℝ := fun x => χ x * α x
  have hχQ : ∀ x, χ x ≠ 0 → ∀ i, (x i - z i).valMinAbs.natAbs + 1 ≤ N := by
    intro x hx i
    have h := lt_of_chi_ne_zero z hD0 x hx i
    have : (x i - z i).valMinAbs.natAbs < N := by exact_mod_cast h
    omega
  have hmemQ : ∀ x, (∀ i, (x i - z i).valMinAbs.natAbs ≤ N) → x ∈ Q := by
    intro x hx
    rw [hQ, mem_cube_iff]
    intro i
    have : (((x i - z i).valMinAbs.natAbs : ℕ) : ℝ) ≤ N := by exact_mod_cast hx i
    linarith
  have hχmem : ∀ x, χ x ≠ 0 → x ∈ Q := by
    intro x hx
    exact hmemQ x fun i => by have := hχQ x hx i; omega
  have hsupp : ∀ x y, (nnGraph d m).Adj x y → χ x ≠ 0 → x ∈ Q ∧ y ∈ Q := by
    intro x y hadj hx
    refine ⟨hχmem x hx, hmemQ y fun i => ?_⟩
    have h1 := adj_dist_le z x y hadj i
    have h2 := hχQ x hx i
    omega
  have hgrad := grad_cutoff_le Q χ w v u D (fun _ => rfl)
    (fun x y => by simp only [w]; ring) (chi_nonneg z _ _) (chi_le_one z _ _)
    (fun x y h => chi_lip z hD0 x y h) hsupp
  have hcG0 := cubeGradient_nonneg' Q v
  have hgrad' : gradientEnergy (nnGraph d m) u ≤
      (2 + 200 * d * Cw) * cubeGradient d m Q v := by
    have hw2 : ∑ y ∈ Q, w y ^ 2 ≤ Cw * (100 * D ^ 2) * cubeGradient d m Q v := by
      refine hμ.trans ?_
      gcongr
    have hS : (∑ y ∈ Q, w y ^ 2) / D ^ 2 ≤ 100 * Cw * cubeGradient d m Q v := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hsumD : ∑ y ∈ Q, w y ^ 2 / D ^ 2 = (∑ y ∈ Q, w y ^ 2) / D ^ 2 :=
      (Finset.sum_div _ _ _).symm
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    have := mul_le_mul_of_nonneg_left hS hd0
    rw [hsumD] at hgrad
    nlinarith
  have hmass : ∑ i ∈ A, a i ^ 2 ≤ ∑ i ∈ Q ∩ A, α i ^ 2 := by
    rw [Finset.inter_comm, ← Finset.sum_ite_mem A Q]
    apply Finset.sum_le_sum
    intro i _
    by_cases hχ : χ i = 0
    · have : a i = 0 := by simp only [a, hχ, zero_mul]
      rw [this]
      split_ifs <;> nlinarith [sq_nonneg (α i)]
    · rw [if_pos (hχmem i hχ)]
      simp only [a]
      rw [mul_pow]
      have : χ i ^ 2 ≤ 1 := by
        nlinarith [chi_nonneg z (N : ℝ) D i, chi_le_one z (N : ℝ) D i]
      nlinarith [sq_nonneg (α i)]
  have hspat : spatialEnergy (nnGraph d m) A b (fun x => a x + u x) ≤
      ∑ i ∈ A, a i ^ 2 + b⁻¹ * gradientEnergy (nnGraph d m) u := by
    unfold spatialEnergy
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨α', v', -, rfl⟩
      exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (mul_nonneg (inv_nonneg.2 hb.le) (gradientEnergy_nonneg' _ _))
    · exact ⟨a, u, fun i _ => rfl, rfl⟩
  have hone : ∀ x ∈ cube d m z R ∩ A, χ x = 1 := by
    intro x hx
    have hxR := (Finset.mem_inter.1 hx).1
    rw [mem_cube_iff] at hxR
    apply chi_eq_one z hD0 x
    intro i
    have h1 : (x i - z i).valMinAbs.natAbs ≤ n := Nat.le_floor (hxR i)
    have h2 : (((x i - z i).valMinAbs.natAbs : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    rw [hD]
    linarith
  refine ⟨fun x => a x + u x, ?_, ?_⟩
  · intro i hi j hj
    simp only [a, u, w, hone i hi, hone j hj]
    ring
  · set S := ∑ i ∈ Q ∩ A, α i ^ 2
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hC1 : 1 ≤ 2 + 200 * (d : ℝ) * Cw := by
      have : 0 ≤ 200 * (d : ℝ) * Cw := by positivity
      linarith
    have hbi : 0 ≤ b⁻¹ := inv_nonneg.2 hb.le
    have h1 := mul_le_mul_of_nonneg_left hgrad' hbi
    have h2 : S ≤ (2 + 200 * (d : ℝ) * Cw) * S := le_mul_of_one_le_left hS0 hC1
    calc spatialEnergy (nnGraph d m) A b (fun x => a x + u x)
        ≤ ∑ i ∈ A, a i ^ 2 + b⁻¹ * gradientEnergy (nnGraph d m) u := hspat
      _ ≤ S + b⁻¹ * ((2 + 200 * d * Cw) * cubeGradient d m Q v) := add_le_add hmass h1
      _ = S + (2 + 200 * d * Cw) * (b⁻¹ * cubeGradient d m Q v) := by ring
      _ ≤ (2 + 200 * d * Cw) * (S + b⁻¹ * cubeGradient d m Q v) := by
        rw [mul_add]
        linarith

end AndersonAC.SolS78
