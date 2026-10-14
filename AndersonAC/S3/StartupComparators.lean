import AndersonAC.S3.Comparators

/-!
The inverse-form comparators at any state delivered by `InitializationInput e₂`
(WP10-facing adapter): if `G` inverts the startup matrix with constant diagonal `r`,
`‖r‖ ≤ C'` and `c' ≤ Im r`, then `G` is the free Green matrix, `r` is a scalar fixed
point in the rectangle `[c', C']`, and `initial_comparators` applies.
-/

noncomputable section
open scoped BigOperators
open AndersonAC.Blueprint

namespace AndersonAC.S3

set_option maxHeartbeats 4000000 in
theorem startup_comparators (hF : TorusFourierStatement) (hC : CirculantCalculusStatement)
    (hLD : LargeSymbolDecayWStatement) {d : ℕ} (hd : 3 ≤ d) {e₂ : ℝ}
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) {c' C' : ℝ} (hc' : 0 < c') (hcC : c' ≤ C') :
    ∃ (nmin : ℕ) (c C C₀ : ℝ), 0 < c ∧ 0 < C ∧ 0 < C₀ ∧
      ∀ n₀ m : ℕ, nmin ≤ n₀ → 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∀ E ∈ OAI.Anderson.energyWindow d e₂, ∀ (r : ℂ)
        (G : Matrix (Torus d (OAI.Anderson.sideLength m))
          (Torus d (OAI.Anderson.sideLength m)) ℂ),
        ‖r‖ ≤ C' → c' ≤ r.im →
        twoSidedInverse
          (OAI.Anderson.periodicHamiltonian 0 (fun _ => ⟨0, by norm_num⟩) - (E : ℂ) • 1 -
            ((OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u : ℝ) : ℂ) •
              Matrix.diagonal (fun _ => r)) G →
        (∀ i, G i i = r) →
        connectedLaplacian (initialD (d := d) (L := OAI.Anderson.sideLength m) E
          (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) r) ∧
        ∀ y : Torus d (OAI.Anderson.sideLength m) → ℂ, neutral y →
          c * (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) ^ 2 *
              form laplacianPlus y ≤
            form (initialX E (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) r) y ∧
          c * normSq y ≤
            form (initialX E (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) r) y ∧
          form (initialX E (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) r) y ≤
            C₀ * normSq y + C * (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) ^ 2 *
              form laplacianPlus y ∧
          form (initialX E (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) r) y ≤
            (1 + Real.rpow (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) kappa) *
              r.im ^ (-2 : ℤ) * normSq y +
              C * (OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u) *
                form laplacianPlus y := by
  set w : ℝ := min (e₂ / 2) (1 / 200) with hwdef
  have hw0 : 0 < w := lt_min (by linarith [he₂.1]) (by norm_num)
  obtain ⟨c, C, C₀, tC, hc, hC0, hC₀, htC, hcomp⟩ :=
    initial_comparators hF hC hLD hd hw0 hc' hcC
  set t₀ : ℝ := tC with ht₀def
  have ht₀ : 0 < t₀ := htC
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / min t₀ 1) (by norm_num : (1 : ℝ) < 4)
  have hmin : 0 < min t₀ 1 := lt_min ht₀ one_pos
  refine ⟨N + 1, c, C, C₀, hc, hC0, hC₀, ?_⟩
  intro n₀ m hn₀ hm u hu E hE
  -- the interface parameter
  set t : ℝ := OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u with htdef
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have h4n : (0 : ℝ) < 4 ^ n₀ := by positivity
  have h4m : (0 : ℝ) < 4 ^ m := by positivity
  have hmn : (4 : ℝ) ^ n₀ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have htpos : 0 < t := by
    simp only [htdef, OAI.Anderson.scaleHeight]; positivity
  have htlow : 1 / (4 : ℝ) ^ (n₀ + 1) < t := by
    have h1 : u / (4 : ℝ) ^ n₀ ≤ t := by
      simp only [htdef, OAI.Anderson.scaleHeight]
      have : 0 ≤ u / (4 : ℝ) ^ m := by positivity
      linarith
    have h2 : 1 / (4 : ℝ) ^ (n₀ + 1) < u / (4 : ℝ) ^ n₀ := by
      rw [pow_succ, div_lt_div_iff₀ (by positivity) h4n]
      nlinarith [hu.1]
    linarith
  have hthigh : t ≤ min t₀ 1 := by
    have h1 : t ≤ 2 / (4 : ℝ) ^ n₀ := by
      simp only [htdef, OAI.Anderson.scaleHeight]
      have e1 : u / (4 : ℝ) ^ n₀ ≤ 1 / 4 ^ n₀ := div_le_div_of_nonneg_right hu.2 h4n.le
      have e2 : u / (4 : ℝ) ^ m ≤ 1 / 4 ^ n₀ :=
        (div_le_div_of_nonneg_right hu.2 h4m.le).trans (div_le_div_of_nonneg_left (by norm_num) h4n hmn)
      have : (2 : ℝ) / 4 ^ n₀ = 1 / 4 ^ n₀ + 1 / 4 ^ n₀ := by ring
      linarith
    have h2 : (2 : ℝ) / 4 ^ n₀ ≤ min t₀ 1 := by
      rw [div_le_iff₀ h4n]
      have hNn : (4 : ℝ) ^ N ≤ 4 ^ n₀ := pow_le_pow_right₀ (by norm_num) (by omega)
      have := (div_lt_iff₀ hmin).mp hN
      nlinarith
    linarith
  have htle1 : t ≤ 1 := hthigh.trans (min_le_right _ _)
  have htt₀ : t ≤ t₀ := hthigh.trans (min_le_left _ _)
  -- the torus side length
  set L : ℕ := OAI.Anderson.sideLength m with hLdef
  have hm1 : 1 ≤ m := by omega
  have hL4 : 4 ≤ L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLeven : Even L := by
    simp only [hLdef, OAI.Anderson.sideLength]
    exact (Nat.even_pow' (by omega)).mpr (by decide)
  have hLbig : t⁻¹ ^ 8 ≤ (L : ℝ) := by
    have h1 : t⁻¹ ≤ (4 : ℝ) ^ (n₀ + 1) := by
      rw [inv_le_comm₀ htpos (by positivity)]
      simpa using htlow.le
    calc t⁻¹ ^ 8 ≤ ((4 : ℝ) ^ (n₀ + 1)) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
      _ = (4 : ℝ) ^ (8 * (n₀ + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ (4 : ℝ) ^ (20 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (L : ℝ) := by simp [hLdef, OAI.Anderson.sideLength]
  intro r G hrn hri hGinv hGdiag
  have hEw : w ≤ E + 2 * d ∧ E + 2 * d ≤ 1 / 100 := by
    have hw1 : w ≤ e₂ / 2 := min_le_left _ _
    have hw2 : w ≤ 1 / 200 := min_le_right _ _
    by_cases h3 : d = 3
    · subst h3
      simp only [OAI.Anderson.energyWindow_three, Set.mem_Ioo] at hE
      push_cast
      constructor <;> linarith [hE.1, hE.2, he₂.2]
    · rw [OAI.Anderson.energyWindow_of_four_le (by omega)] at hE
      simp only [OAI.Anderson.higherDimWindow, Set.mem_Ioo] at hE
      constructor <;> linarith [hE.1, hE.2]
  have hrim : 0 < r.im := lt_of_lt_of_le hc' hri
  set z : ℂ := (E : ℂ) + (t : ℂ) * r with hz
  obtain ⟨hFinv, -⟩ := hF d L hL4
  obtain ⟨hinv, hdiag⟩ := hFinv z (resolvent_z_ne htpos hrim)
  have hmat : OAI.Anderson.periodicHamiltonian 0 (fun _ => ⟨0, by norm_num⟩) - (E : ℂ) • 1 -
      ((t : ℝ) : ℂ) • Matrix.diagonal (fun _ => r) =
      freeHopping (d := d) (L := L) - z • (1 : Matrix (Torus d L) (Torus d L) ℂ) := by
    rw [periodicHamiltonian_zero_eq]
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, hz]
    split_ifs <;> ring
  rw [htdef] at hmat
  rw [hmat] at hGinv
  have hGeq : G = freeGreen z := by
    calc G = G * 1 := (Matrix.mul_one G).symm
      _ = G * ((freeHopping - z • 1) * freeGreen z) := by rw [hinv.1]
      _ = (G * (freeHopping - z • 1)) * freeGreen z := (Matrix.mul_assoc _ _ _).symm
      _ = freeGreen z := by rw [hGinv.2, Matrix.one_mul]
  have hfix : scalarMap (d := d) (L := L) E t r = r := by
    have h0 := hGdiag 0
    rw [hGeq, hdiag 0] at h0
    refine Eq.trans ?_ h0
    simp only [scalarMap]
    congr 1
    funext k
    simp only [gridResolvent, hz, sub_add_eq_sub_sub]
  have hrect : r ∈ rectangle c' C' :=
    ⟨(Complex.abs_re_le_norm r).trans hrn, hri, (Complex.im_le_norm r).trans hrn⟩
  exact hcomp t htpos htt₀ L hL4 hLeven hLbig
    E hEw.1 hEw.2 r hrect hfix
