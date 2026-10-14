import AndersonAC.S3.Definitions
import AndersonAC.S3H.Fourier
import AndersonAC.S3H.Quadrature
import AndersonAC.S3H.Lattice
import AndersonAC.S3.GridCount

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS3
open AndersonAC.S3

variable {d L : ℕ} [NeZero L]

lemma fourier_shift (v : Torus d L → ℂ) (a k : Torus d L) :
    AndersonAC.S3.fourier (fun x => v (x + a)) k =
      character k a * AndersonAC.S3.fourier v k := by
  unfold AndersonAC.S3.fourier
  rw [← Equiv.sum_comp (Equiv.addRight (-a))]
  simp_rw [Equiv.coe_addRight]
  calc
    (∑ x, v ((x + -a) + a) * star (character k (x + -a)))
        = ∑ x, v x * star (character k (x + -a)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [show (x + -a) + a = x by abel]
    _ = ∑ x, character k a * (v x * star (character k x)) := by
          apply Finset.sum_congr rfl
          intro x _
          have hc : star (character k (x + -a)) =
              character k a * star (character k x) := by
            rw [charAddX, charNegX, star_mul, star_star]
          rw [hc]
          ring
    _ = character k a * ∑ x, v x * star (character k x) := by
          rw [Finset.mul_sum]

lemma fourier_difference (v : Torus d L → ℂ) (a k : Torus d L) :
    AndersonAC.S3.fourier (fun x => v (x + a) - v x) k =
      (character k a - 1) * AndersonAC.S3.fourier v k := by
  calc
    AndersonAC.S3.fourier (fun x => v (x + a) - v x) k
        = AndersonAC.S3.fourier (fun x => v (x + a)) k -
            AndersonAC.S3.fourier v k := by
              unfold AndersonAC.S3.fourier
              change (∑ x, (v (x + a) - v x) * star (character k x)) =
                (∑ x, v (x + a) * star (character k x)) -
                  (∑ x, v x * star (character k x))
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro x _
              rw [sub_mul]
    _ = (character k a - 1) * AndersonAC.S3.fourier v k := by
          rw [fourier_shift]
          ring

lemma difference_normSq_parseval (v : Torus d L → ℂ) (a : Torus d L) :
    normSq (fun x => v (x + a) - v x) =
      gridAvgReal (fun k => ‖character k a - 1‖ ^ 2 *
        ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
  rw [AndersonAC.S3.parseval]
  congr 1
  funext k
  rw [fourier_difference, norm_mul]
  ring

lemma character_step_normSq (hL : 4 ≤ L) (k : Torus d L) (j : Fin d) :
    ‖character k (basisStep j) - 1‖ ^ 2 =
      4 * Real.sin (gridAngle k j / 2) ^ 2 := by
  rw [charBasis k j (by omega)]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [norm_mul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  norm_num

lemma fourier_gradientEnergy (hL : 4 ≤ L) (v : Torus d L → ℂ) :
    gradientEnergy v = gridAvgReal (fun k =>
      laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
  change (∑ x, ∑ j : Fin d,
      ‖v (x + basisStep j) - v x‖ ^ 2) = _
  rw [Finset.sum_comm]
  change (∑ j : Fin d,
      normSq (fun x => v (x + basisStep j) - v x)) = _
  simp_rw [difference_normSq_parseval, character_step_normSq hL]
  unfold gridAvgReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext k
  have hN : (Fintype.card (Torus d L) : ℝ)⁻¹ ≠ 0 := by positivity
  rw [← Finset.mul_sum]
  apply mul_left_cancel₀ hN
  have hs : (∑ j : Fin d, 4 * Real.sin (gridAngle k j / 2) ^ 2) =
      4 * (∑ j : Fin d, Real.sin (gridAngle k j / 2) ^ 2) := by
    rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, hs]
  simp [laplacianSymbol]

lemma int_cast_abs_ge_one {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hn : 1 ≤ z.natAbs := by omega
  have hnR : (1 : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hnR

lemma exists_centerInt_ne_zero {k : Torus d L} (hk : k ≠ 0) :
    ∃ j : Fin d, centerInt L (k j) ≠ 0 := by
  by_contra h
  push Not at h
  apply hk
  funext j
  have hc := centerInt_cast (k j)
  rw [h j] at hc
  simpa using hc.symm

lemma gridAngle_abs_lower {k : Torus d L} (hL : 4 ≤ L)
    (j : Fin d) (hj : centerInt L (k j) ≠ 0) :
    2 * Real.pi / (L : ℝ) ≤ |gridAngle k j| := by
  have hLpos : (0 : ℝ) < L := by positivity
  have hfac : 0 < 2 * Real.pi / (L : ℝ) := by positivity
  have hm := int_cast_abs_ge_one (z := centerInt L (k j)) hj
  have hform := gridAngle_eq_centerInt (k := k) (j := j)
  have heq : |gridAngle k j| =
      (2 * Real.pi / (L : ℝ)) * |((centerInt L (k j) : ℤ) : ℝ)| := by
    rw [hform]
    have hmul : 2 * Real.pi * ((centerInt L (k j) : ℤ) : ℝ) / (L : ℝ) =
        (2 * Real.pi / (L : ℝ)) * ((centerInt L (k j) : ℤ) : ℝ) := by ring
    rw [hmul, abs_mul, abs_of_pos hfac]
  rw [heq]
  nlinarith

lemma laplacianSymbol_lower_nonzero (hL : 4 ≤ L) {k : Torus d L} (hk : k ≠ 0) :
    16 / (L : ℝ) ^ 2 ≤ laplacianSymbol (gridAngle k) := by
  obtain ⟨j, hj⟩ := exists_centerInt_ne_zero hk
  have hθ := gridAngle_abs_lower hL j hj
  have hb := AndersonAC.S3.angle1_bounds (k j)
  have hθbound : |gridAngle k j| ≤ Real.pi := by
    rw [gridAngle_apply]
    exact abs_le.mpr ⟨hb.1, hb.2.le⟩
  have hhalf : |gridAngle k j / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hθbound
  have hsin := Real.mul_abs_le_abs_sin hhalf
  have hratio : 2 / (L : ℝ) ≤ |Real.sin (gridAngle k j / 2)| := by
    have hθmul : 2 * Real.pi ≤ |gridAngle k j| * (L : ℝ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < L)).mp hθ
    have hratio' : 2 / (L : ℝ) ≤ |gridAngle k j| / Real.pi := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < L) Real.pi_pos]
      exact hθmul
    have heq : 2 / Real.pi * |gridAngle k j / 2| =
        |gridAngle k j| / Real.pi := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      2 / (L : ℝ) ≤ |gridAngle k j| / Real.pi := hratio'
      _ = 2 / Real.pi * |gridAngle k j / 2| := heq.symm
      _ ≤ |Real.sin (gridAngle k j / 2)| := hsin
  have hsin2 : 16 / (L : ℝ) ^ 2 ≤
      4 * Real.sin (gridAngle k j / 2) ^ 2 := by
    have hsqAbs : (2 / (L : ℝ)) ^ 2 ≤
        |Real.sin (gridAngle k j / 2)| ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (by positivity) hratio
    have hsq : (2 / (L : ℝ)) ^ 2 ≤
        Real.sin (gridAngle k j / 2) ^ 2 := by
      simpa [sq_abs] using hsqAbs
    have heq : 16 / (L : ℝ) ^ 2 = 4 * (2 / (L : ℝ)) ^ 2 := by
      field_simp
      ring
    rw [heq]
    nlinarith [hsq]
  have hsum : Real.sin (gridAngle k j / 2) ^ 2 ≤
      ∑ i : Fin d, Real.sin (gridAngle k i / 2) ^ 2 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin d => Real.sin (gridAngle k i / 2) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  unfold laplacianSymbol
  exact hsin2.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

lemma fourier_zero_eq_sum (v : Torus d L → ℂ) :
    AndersonAC.S3.fourier v 0 = ∑ x, v x := by
  unfold AndersonAC.S3.fourier
  simp [char_zero_freq]

theorem torus_poincare_proof (_hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ v : Torus d L → ℂ, neutral v →
        normSq v ≤ C * (L : ℝ) ^ 2 * gradientEnergy v := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro L inst hL v hv
  have hzero : AndersonAC.S3.fourier v 0 = 0 := by
    rw [fourier_zero_eq_sum]
    exact hv
  have hmode : ∀ k : Torus d L,
      ‖AndersonAC.S3.fourier v k‖ ^ 2 ≤
        ((L : ℝ) ^ 2 / 16) *
          (laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [hzero, laplacianSymbol, gridAngle]
    · have hgap := laplacianSymbol_lower_nonzero hL hk
      have hcoef : 1 ≤ (L : ℝ) ^ 2 / 16 * laplacianSymbol (gridAngle k) := by
        have hscale : 0 ≤ (L : ℝ) ^ 2 / 16 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hgap hscale
        have hinv : (L : ℝ) ^ 2 / 16 * (16 / (L : ℝ) ^ 2) = 1 := by
          field_simp
        nlinarith
      have hnonneg := sq_nonneg ‖AndersonAC.S3.fourier v k‖
      nlinarith
  have havg : gridAvgReal (fun k => ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
      ((L : ℝ) ^ 2 / 16) * gridAvgReal (fun k =>
        laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    unfold gridAvgReal
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hmode k)
    have hsum' : (∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
        ((L : ℝ) ^ 2 / 16) *
          (∑ k, laplacianSymbol (gridAngle k) *
            ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
      calc
        (∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2)
            ≤ ∑ k, ((L : ℝ) ^ 2 / 16) *
                (laplacianSymbol (gridAngle k) *
                  ‖AndersonAC.S3.fourier v k‖ ^ 2) := hsum
        _ = _ := by rw [← Finset.mul_sum]
    have hN : 0 ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card (Torus d L) : ℝ)⁻¹ *
          ∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2
        ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ *
            (((L : ℝ) ^ 2 / 16) *
              ∑ k, laplacianSymbol (gridAngle k) *
                ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hsum' hN
      _ = ((L : ℝ) ^ 2 / 16) *
            ((Fintype.card (Torus d L) : ℝ)⁻¹ *
              ∑ k, laplacianSymbol (gridAngle k) *
                ‖AndersonAC.S3.fourier v k‖ ^ 2) := by ring
  calc
    normSq v = gridAvgReal (fun k => ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
      AndersonAC.S3.parseval v
    _ ≤ ((L : ℝ) ^ 2 / 16) * gradientEnergy v := by
      rw [fourier_gradientEnergy hL v]
      exact havg
    _ = (1 / 16) * (L : ℝ) ^ 2 * gradientEnergy v := by ring

def foldFinEquiv {l : ℕ} (hl : 0 < l) : Fin (2 * l) ≃ Fin l × Fin 2 where
  toFun x :=
    (⟨if x.val < l then x.val else 2 * l - 1 - x.val, by
      split_ifs <;> omega⟩,
      ⟨if x.val < l then 0 else 1, by split_ifs <;> omega⟩)
  invFun p :=
    if p.2.val = 0 then ⟨p.1.val, by omega⟩
    else ⟨2 * l - 1 - p.1.val, by omega⟩
  left_inv := by
    intro x
    apply Fin.ext
    by_cases hx : x.val < l
    · simp [hx]
    · simp [hx]
      omega
  right_inv := by
    rintro ⟨i, b⟩
    have hi := i.isLt
    have hn : l ≤ 2 * l - 1 - i.val := by omega
    have hcalc : 2 * l - 1 - (2 * l - 1 - i.val) = i.val := by omega
    fin_cases b <;> apply Prod.ext
    · apply Fin.ext
      simp [hi]
    · apply Fin.ext
      simp [hi]
    · apply Fin.ext
      simp [hn, hcalc]
    · apply Fin.ext
      simp [hn]

def foldFiberEquiv {l : ℕ} (hl : 0 < l) [NeZero (2 * l)] :
    ZMod (2 * l) ≃ Fin l × Fin 2 :=
  (ZMod.finEquiv (2 * l)).toEquiv.symm.trans (foldFinEquiv hl)

lemma finEquiv_symm_val {n : ℕ} [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rfl

def foldPiEquiv {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)] :
    Torus d (2 * l) ≃ Cube d l × (Fin d → Fin 2) where
  toFun x :=
    ((fun j => (foldFiberEquiv hl (x j)).1),
      (fun j => (foldFiberEquiv hl (x j)).2))
  invFun p := fun j => (foldFiberEquiv hl).symm (p.1 j, p.2 j)
  left_inv := by
    intro x
    funext j
    exact (foldFiberEquiv hl).left_inv (x j)
  right_inv := by
    rintro ⟨y, b⟩
    apply Prod.ext <;> funext j <;> simp

lemma foldFiberEquiv_fst {l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (x : ZMod (2 * l)) :
    (foldFiberEquiv hl x).1 = ⟨foldCoordinate l x, by
      have hx := x.val_lt
      unfold foldCoordinate
      split_ifs <;> omega⟩ := by
  apply Fin.ext
  have hval := finEquiv_symm_val x
  simp [foldFiberEquiv, foldFinEquiv, foldCoordinate, hval]

lemma foldPiEquiv_fst {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (x : Torus d (2 * l)) :
    (foldPiEquiv hl x).1 = fun j => ⟨foldCoordinate l (x j), by
      have hx := (x j).val_lt
      unfold foldCoordinate
      split_ifs <;> omega⟩ := by
  funext j
  exact foldFiberEquiv_fst hl (x j)

lemma foldPi_sum {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (f : Cube d l → ℂ) :
    (∑ x : Torus d (2 * l), f (foldPiEquiv hl x).1) =
      (2 : ℂ) ^ d * ∑ y, f y := by
  calc
    (∑ x : Torus d (2 * l), f (foldPiEquiv hl x).1)
        = ∑ p : Cube d l × (Fin d → Fin 2), f p.1 := by
          refine Fintype.sum_equiv (foldPiEquiv hl) _ _ (fun x => ?_)
          rfl
    _ = (2 : ℂ) ^ d * ∑ y, f y := by
          rw [Fintype.sum_prod_type]
          simp [Fintype.card_fin, Finset.sum_const, Finset.mul_sum]

lemma cube_centered_sum {d l : ℕ} (hl : 0 < l) (v : Cube d l → ℂ) :
    (∑ y, (v y - cubeMean v)) = 0 := by
  letI : Nonempty (Cube d l) := ⟨fun _ => ⟨0, hl⟩⟩
  have hsum : (∑ y, (v y - cubeMean v)) =
      (∑ y, v y) - (Fintype.card (Cube d l) : ℂ) * cubeMean v := by
    simp [Finset.sum_sub_distrib]
  have hcard : (Fintype.card (Cube d l) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Cube d l)).ne'
  rw [hsum]
  unfold cubeMean
  field_simp
  ring

lemma reflected_neutral {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (v : Cube d l → ℂ) : neutral (reflected hl v) := by
  unfold neutral
  calc
    (∑ x : Torus d (2 * l), reflected hl v x)
        = ∑ x, (v (foldPiEquiv hl x).1 - cubeMean v) := by
          apply Finset.sum_congr rfl
          intro x _
          simp [reflected, foldPiEquiv_fst]
    _ = (2 : ℂ) ^ d * (∑ y, (v y - cubeMean v)) := by
          rw [foldPi_sum hl (fun y => v y - cubeMean v)]
    _ = 0 := by rw [cube_centered_sum hl]; simp

lemma centerInt_natAbs_eq_valMinAbs {L : ℕ} [NeZero L] (x : ZMod L) :
    (centerInt L x).natAbs = x.valMinAbs.natAbs := by
  rw [centerInt, ZMod.valMinAbs_def_pos]
  by_cases h : 2 * x.val < L
  · have hh : x.val ≤ L / 2 := by omega
    simp [h, hh]
  · by_cases hh : x.val ≤ L / 2
    · have heq : 2 * x.val = L := by omega
      rw [if_neg h, if_pos hh]
      have hcast : (x.val : ℤ) - (L : ℤ) = -(x.val : ℤ) := by omega
      rw [hcast, Int.natAbs_neg]
    · simp [h, hh]

lemma centerInt_natAbs_eq_coordMin {d L : ℕ} [NeZero L]
    (k : Torus d L) (j : Fin d) :
    (centerInt L (k j)).natAbs = AndersonAC.S3.coordMin 0 k j := by
  have hm := ZMod.valMinAbs_natAbs_eq_min (a := -(k j))
  have hm' : AndersonAC.S3.coordMin (0 : Torus d L) k j =
      (-(k j)).valMinAbs.natAbs := by
    simpa [AndersonAC.S3.coordMin] using hm.symm
  rw [ZMod.natAbs_valMinAbs_neg] at hm'
  rw [centerInt_natAbs_eq_valMinAbs]
  exact hm'.symm

lemma torusDistance_eq_centerInt_sum {d L : ℕ} [NeZero L] (k : Torus d L) :
    torusDistance (0 : Torus d L) k =
      ∑ j : Fin d, (centerInt L (k j)).natAbs := by
  rw [AndersonAC.S3.torusDistance_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (centerInt_natAbs_eq_coordMin k j).symm

lemma torusDistance_zero_iff {d L : ℕ} [NeZero L] (k : Torus d L) :
    torusDistance (0 : Torus d L) k = 0 ↔ k = 0 := by
  constructor
  · intro hdist
    rw [torusDistance_eq_centerInt_sum] at hdist
    have hz : ∀ j : Fin d, (centerInt L (k j)).natAbs = 0 := by
      intro j
      have hle : (centerInt L (k j)).natAbs ≤
          ∑ i : Fin d, (centerInt L (k i)).natAbs :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin d => (centerInt L (k i)).natAbs)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hdist] at hle
      omega
    funext j
    have hj : centerInt L (k j) = 0 := (Int.natAbs_eq_zero).mp (hz j)
    have hc := centerInt_cast (k j)
    rw [hj] at hc
    simpa using hc.symm
  · rintro rfl
    simp [torusDistance]

lemma laplacianSymbol_lower_distance (hd : 3 ≤ d) (hL : 4 ≤ L)
    (k : Torus d L) :
    (16 / ((d : ℝ) * (L : ℝ) ^ 2)) *
        (torusDistance (0 : Torus d L) k : ℝ) ^ 2 ≤
      laplacianSymbol (gridAngle k) := by
  have hLpos : (0 : ℝ) < L := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let mAbs : Fin d → ℝ := fun j =>
    (((centerInt L (k j)).natAbs : ℕ) : ℝ)
  have hterm : ∀ j : Fin d,
      16 / (L : ℝ) ^ 2 * mAbs j ^ 2 ≤
        4 * Real.sin (gridAngle k j / 2) ^ 2 := by
    intro j
    have hbound := AndersonAC.S3.angle1_bounds (k j)
    have hθbound : |gridAngle k j| ≤ Real.pi := by
      rw [AndersonAC.S3.gridAngle_apply]
      exact abs_le.mpr ⟨hbound.1, hbound.2.le⟩
    have hhalf : |gridAngle k j / 2| ≤ Real.pi / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hθbound
    have hsin := Real.mul_abs_le_abs_sin hhalf
    have hθabs : |gridAngle k j| = (2 * Real.pi / (L : ℝ)) * mAbs j := by
      rw [gridAngle_eq_centerInt]
      have hm : |((centerInt L (k j) : ℤ) : ℝ)| = mAbs j := by
        simp [mAbs, Nat.cast_natAbs, Int.cast_abs]
      have hfac : 0 < 2 * Real.pi / (L : ℝ) := by positivity
      have heq : 2 * Real.pi * ((centerInt L (k j) : ℤ) : ℝ) /
          (L : ℝ) = (2 * Real.pi / (L : ℝ)) *
            ((centerInt L (k j) : ℤ) : ℝ) := by ring
      rw [heq, abs_mul, abs_of_pos hfac, hm]
    have hratio : 2 / (L : ℝ) * mAbs j ≤
        |Real.sin (gridAngle k j / 2)| := by
      have heq : 2 / Real.pi * |gridAngle k j / 2| =
          2 / (L : ℝ) * mAbs j := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [hθabs]
        field_simp [Real.pi_ne_zero]
      rw [← heq]
      exact hsin
    have hsq : (2 / (L : ℝ) * mAbs j) ^ 2 ≤
        Real.sin (gridAngle k j / 2) ^ 2 := by
      simpa [pow_two, sq_abs] using
        mul_self_le_mul_self (by positivity) hratio
    have heq : 16 / (L : ℝ) ^ 2 * mAbs j ^ 2 =
        4 * (2 / (L : ℝ) * mAbs j) ^ 2 := by
      field_simp
      ring
    rw [heq]
    nlinarith
  have hcs : (∑ j : Fin d, mAbs j) ^ 2 ≤
      (d : ℝ) * ∑ j : Fin d, mAbs j ^ 2 := by
    simpa [mAbs, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun j : Fin d => mAbs j))
  have hdist : (torusDistance (0 : Torus d L) k : ℝ) =
      ∑ j : Fin d, mAbs j := by
    rw [torusDistance_eq_centerInt_sum]
    simp [mAbs]
  have hdistSq :
      (torusDistance (0 : Torus d L) k : ℝ) ^ 2 / (d : ℝ) ≤
        ∑ j : Fin d, mAbs j ^ 2 := by
    rw [hdist]
    exact (div_le_iff₀ hdpos).2 (by simpa [mul_comm] using hcs)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  calc
    (16 / ((d : ℝ) * (L : ℝ) ^ 2)) *
        (torusDistance (0 : Torus d L) k : ℝ) ^ 2
        = (16 / (L : ℝ) ^ 2) *
            ((torusDistance (0 : Torus d L) k : ℝ) ^ 2 / (d : ℝ)) := by
              field_simp
    _ ≤ (16 / (L : ℝ) ^ 2) * ∑ j : Fin d, mAbs j ^ 2 :=
          mul_le_mul_of_nonneg_left hdistSq (by positivity)
    _ = ∑ j : Fin d, 16 / (L : ℝ) ^ 2 * mAbs j ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin d, 4 * Real.sin (gridAngle k j / 2) ^ 2 := hsum
    _ = laplacianSymbol (gridAngle k) := by
          simp only [laplacianSymbol]
          rw [← Finset.mul_sum]

lemma shell_inverse_sum_bound {d : ℕ} (hd : 3 ≤ d) (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R,
        (1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2) ≤
      (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2) := by
  by_cases hR : R = 0
  · simp [hR]
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  have hcard : (Finset.Icc 1 R).card = R := by simp
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      (1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2 ≤
        (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 3) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr1)
    have hbase : (1 : ℝ) + r ≤ 2 * r := by exact_mod_cast (by omega : 1 + r ≤ 2 * r)
    have hpow : (1 + (r : ℝ)) ^ (d - 1) ≤ (2 * r) ^ (d - 1) := by
      exact pow_le_pow_left₀ (by positivity) hbase (d - 1)
    have hexp : d - 1 = (d - 3) + 2 := by omega
    have hrpow : (r : ℝ) ^ (d - 1) = (r : ℝ) ^ (d - 3) * (r : ℝ) ^ 2 := by
      rw [hexp, pow_add]
    have htwo : (2 : ℝ) ^ (d - 1) * (r : ℝ) ^ (d - 3) * (r : ℝ) ^ 2 =
        (2 * (r : ℝ)) ^ (d - 1) := by
      rw [mul_pow, hrpow]
      ring
    have hscale : (r : ℝ) ^ (d - 3) ≤ (R : ℝ) ^ (d - 3) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hrR) (d - 3)
    calc
      (1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2
          ≤ (2 * (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hpow (sq_nonneg _)
      _ = (2 : ℝ) ^ (d - 1) * (r : ℝ) ^ (d - 3) := by
            rw [← htwo]
            field_simp [ne_of_gt hrpos]
      _ ≤ (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 3) :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ r ∈ Finset.Icc 1 R,
        (1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2)
        ≤ ∑ r ∈ Finset.Icc 1 R,
            (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 3) := hsum
    _ = (R : ℝ) * ((2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 3)) := by simp [hcard]
    _ = (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2) := by
          have hexp : d - 2 = (d - 3) + 1 := by omega
          rw [hexp, pow_succ]
          ring

theorem low_frequency_inverse_sum_bound (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        gridAvgReal (fun k : Torus d L =>
          if 1 ≤ torusDistance (0 : Torus d L) k ∧
              torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊ then
            (laplacianSymbol (gridAngle k))⁻¹ else 0) ≤ C * a := by
  obtain ⟨Cs, hCs, hShell⟩ := AndersonAC.S3.lattice_shell_count_proof hd
  refine ⟨Cs * (d : ℝ) / 16 * 2 ^ (d - 1), by positivity, ?_⟩
  intro L inst hL a ha0 ha1
  let R : ℕ := ⌊a * (L : ℝ)⌋₊
  let dist : Torus d L → ℕ := fun k => torusDistance (0 : Torus d L) k
  let lam : Torus d L → ℝ := fun k => laplacianSymbol (gridAngle k)
  let low : Finset (Torus d L) := Finset.univ.filter (fun k => 1 ≤ dist k ∧ dist k ≤ R)
  have hRnonneg : (0 : ℝ) ≤ a * (L : ℝ) := by positivity
  have hRfloor : (R : ℝ) ≤ a * (L : ℝ) := by
    exact Nat.floor_le hRnonneg
  have hlowCast : (∑ k : Torus d L,
      (if k ∈ low then (lam k)⁻¹ else 0)) = ∑ k ∈ low, (lam k)⁻¹ := by
    simpa [low] using (Finset.sum_ite_mem_eq (s := low)
      (f := fun k : Torus d L => (lam k)⁻¹))
  have hMaps : ∀ k ∈ low, dist k ∈ Finset.Icc 1 R := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact Finset.mem_Icc.mpr hk'
  have hPart :
      (∑ r ∈ Finset.Icc 1 R, ∑ k ∈ low with dist k = r, (lam k)⁻¹) =
        ∑ k ∈ low, (lam k)⁻¹ := by
    exact Finset.sum_fiberwise_of_maps_to hMaps _
  have hFiber : ∀ r ∈ Finset.Icc 1 R,
      (∑ k ∈ low with dist k = r, (lam k)⁻¹) ≤
        Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
          ((1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2) := by
    intro r hr
    let fiber := low.filter (fun k => dist k = r)
    let full := Finset.univ.filter (fun k : Torus d L => dist k = r)
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrpos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
    have hsubset : fiber ⊆ full := by
      intro k hk
      have hkr := (Finset.mem_filter.mp hk).2
      simp [fiber, full, hkr]
    have hcount : (full.card : ℝ) ≤ Cs * (1 + (r : ℝ)) ^ (d - 1) := by
      simpa [full, dist] using hShell L hL (0 : Torus d L) r
    let B : ℝ := (d : ℝ) * (L : ℝ) ^ 2 / (16 * (r : ℝ) ^ 2)
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hInv : ∀ k ∈ fiber, (lam k)⁻¹ ≤ B := by
      intro k hk
      have hkr := (Finset.mem_filter.mp hk).2
      have hlow := laplacianSymbol_lower_distance hd hL k
      have hLambda : 16 / ((d : ℝ) * (L : ℝ) ^ 2) * (r : ℝ) ^ 2 ≤ lam k := by
        simpa [lam, dist, hkr] using hlow
      have hpos : 0 < 16 / ((d : ℝ) * (L : ℝ) ^ 2) * (r : ℝ) ^ 2 := by
        positivity
      calc
        (lam k)⁻¹ ≤
            (16 / ((d : ℝ) * (L : ℝ) ^ 2) * (r : ℝ) ^ 2)⁻¹ :=
              inv_anti₀ hpos hLambda
        _ = B := by
              dsimp [B]
              field_simp
    have hsumB : (∑ k ∈ fiber, (lam k)⁻¹) ≤ (fiber.card : ℝ) * B := by
      calc
        (∑ k ∈ fiber, (lam k)⁻¹) ≤ ∑ k ∈ fiber, B := by
          apply Finset.sum_le_sum
          intro k hk
          exact hInv k hk
        _ = (fiber.card : ℝ) * B := by simp
    have hcard : (fiber.card : ℝ) ≤ (full.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hsumCount : (∑ k ∈ fiber, (lam k)⁻¹) ≤
        Cs * (1 + (r : ℝ)) ^ (d - 1) * B := by
      exact hsumB.trans (mul_le_mul_of_nonneg_right hcard hBpos.le |>.trans
        (mul_le_mul_of_nonneg_right hcount hBpos.le))
    simpa [B, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsumCount
  have hLowSum : (∑ k ∈ low, (lam k)⁻¹) ≤
      Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
        (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2) := by
    rw [← hPart]
    calc
      (∑ r ∈ Finset.Icc 1 R,
          ∑ k ∈ low with dist k = r, (lam k)⁻¹)
        ≤ ∑ r ∈ Finset.Icc 1 R,
            Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
              ((1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2) := by
                apply Finset.sum_le_sum
                intro r hr
                exact hFiber r hr
      _ = Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
            (∑ r ∈ Finset.Icc 1 R,
              (1 + (r : ℝ)) ^ (d - 1) / (r : ℝ) ^ 2) := by
              rw [← Finset.mul_sum]
      _ ≤ Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
            ((2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2)) := by
              exact mul_le_mul_of_nonneg_left
                (shell_inverse_sum_bound hd R) (by positivity)
      _ = _ := by ring
  have hcardTor : (Fintype.card (Torus d L) : ℝ) = (L : ℝ) ^ d := by
    simp [Torus]
  have hRratio : (R : ℝ) / (L : ℝ) ≤ a := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < L)]
    exact hRfloor
  have hRatioPow : ((R : ℝ) / (L : ℝ)) ^ (d - 2) ≤ a ^ (d - 2) := by
    exact pow_le_pow_left₀ (by positivity) hRratio (d - 2)
  have haPow : a ^ (d - 2) ≤ a := by
    have hnpos : 0 < d - 2 := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    rw [hn, pow_succ]
    calc
      a ^ n * a = a * a ^ n := by ring
      _ ≤ a := mul_le_of_le_one_right ha0.le (pow_le_one₀ ha0.le ha1)
  have hconst :
      (Fintype.card (Torus d L) : ℝ)⁻¹ *
        (Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
          (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2)) =
        (Cs * (d : ℝ) / 16 * 2 ^ (d - 1)) *
          ((R : ℝ) / (L : ℝ)) ^ (d - 2) := by
    rw [hcardTor, div_pow]
    have hLne : (L : ℝ) ≠ 0 := by positivity
    have he : d = (d - 2) + 2 := by omega
    rw [he, pow_add]
    field_simp [hLne]
    have hexp : (d - 2) + 2 - 2 = d - 2 := by omega
    rw [hexp]
    ring
  change (Fintype.card (Torus d L) : ℝ)⁻¹ *
      ∑ k : Torus d L,
        (if 1 ≤ dist k ∧ dist k ≤ R then (lam k)⁻¹ else 0) ≤
      (Cs * (d : ℝ) / 16 * 2 ^ (d - 1)) * a
  have hlowCast' : (∑ k : Torus d L,
      (if 1 ≤ dist k ∧ dist k ≤ R then (lam k)⁻¹ else 0)) =
        ∑ k ∈ low, (lam k)⁻¹ := by
    simpa [low] using hlowCast
  rw [hlowCast']
  calc
    (Fintype.card (Torus d L) : ℝ)⁻¹ * ∑ k ∈ low, (lam k)⁻¹
        ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ *
            (Cs * ((d : ℝ) * (L : ℝ) ^ 2 / 16) *
              (2 : ℝ) ^ (d - 1) * (R : ℝ) ^ (d - 2)) :=
                mul_le_mul_of_nonneg_left hLowSum (by positivity)
    _ = (Cs * (d : ℝ) / 16 * 2 ^ (d - 1)) *
          ((R : ℝ) / (L : ℝ)) ^ (d - 2) := hconst
    _ ≤ (Cs * (d : ℝ) / 16 * 2 ^ (d - 1)) * a := by
          exact mul_le_mul_of_nonneg_left (hRatioPow.trans haPow) (by positivity)

lemma fourier_sub_local {d L : ℕ} [NeZero L]
    (f g : Torus d L → ℂ) (k : Torus d L) :
    AndersonAC.S3.fourier (fun x => f x - g x) k =
      AndersonAC.S3.fourier f k - AndersonAC.S3.fourier g k := by
  unfold AndersonAC.S3.fourier
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [sub_mul]

lemma synthesis_fourier (v : Torus d L → ℂ) :
    AndersonAC.S3.synthesis (AndersonAC.S3.fourier v) = v := by
  let u : Torus d L → ℂ := fun x =>
    AndersonAC.S3.synthesis (AndersonAC.S3.fourier v) x - v x
  have hu : ∀ k, AndersonAC.S3.fourier u k = 0 := by
    intro k
    change AndersonAC.S3.fourier
      (fun x => AndersonAC.S3.synthesis (AndersonAC.S3.fourier v) x - v x) k = 0
    rw [fourier_sub_local, AndersonAC.S3.fourier_synthesis]
    simp
  have hnorm : normSq u = 0 := by
    rw [AndersonAC.S3.parseval]
    unfold gridAvgReal
    simp_rw [hu]
    simp
  funext x
  have hle : ‖u x‖ ^ 2 ≤ normSq u := by
    unfold normSq
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Torus d L => ‖u i‖ ^ 2)
      (fun i _ => sq_nonneg ‖u i‖) (Finset.mem_univ x)
  have hzero : ‖u x‖ = 0 := by nlinarith
  have hux : u x = 0 := norm_eq_zero.mp hzero
  dsimp [u] at hux
  exact sub_eq_zero.mp hux

noncomputable def fourierBandPart {d L : ℕ} [NeZero L]
    (S : Finset (Torus d L)) (v : Torus d L → ℂ) (x : Torus d L) : ℂ :=
  AndersonAC.S3.gridAvg (fun k =>
    if k ∈ S then AndersonAC.S3.character k x * AndersonAC.S3.fourier v k else 0)

noncomputable def fourierBandComplement {d L : ℕ} [NeZero L]
    (S : Finset (Torus d L)) (v : Torus d L → ℂ) (x : Torus d L) : ℂ :=
  AndersonAC.S3.gridAvg (fun k =>
    if k ∉ S then AndersonAC.S3.character k x * AndersonAC.S3.fourier v k else 0)

lemma gridAvg_add_local {d L : ℕ} [NeZero L]
    (f g : Torus d L → ℂ) :
    AndersonAC.S3.gridAvg f + AndersonAC.S3.gridAvg g =
      AndersonAC.S3.gridAvg (fun k => f k + g k) := by
  unfold AndersonAC.S3.gridAvg
  rw [Finset.sum_add_distrib]
  ring

lemma fourierBandPart_add_complement {d L : ℕ} [NeZero L]
    (S : Finset (Torus d L)) (v : Torus d L → ℂ) (x : Torus d L) :
    fourierBandPart S v x + fourierBandComplement S v x =
      AndersonAC.S3.synthesis (AndersonAC.S3.fourier v) x := by
  unfold fourierBandPart fourierBandComplement AndersonAC.S3.synthesis
  rw [gridAvg_add_local]
  congr 1
  funext k
  by_cases hk : k ∈ S <;> simp [hk]

lemma weighted_cauchy_finset {α : Type*} (s : Finset α)
    (w : α → ℝ) (z : α → ℂ) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, ‖z i‖) ^ 2 ≤
      (∑ i ∈ s, (w i)⁻¹) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact inv_nonneg.mpr (le_of_lt (hw i hi))
  · intro i hi
    exact mul_nonneg (le_of_lt (hw i hi)) (sq_nonneg ‖z i‖)
  · intro i hi
    have hwi := hw i hi
    have heq : ‖z i‖ ^ 2 = (w i)⁻¹ * (w i * ‖z i‖ ^ 2) := by
      field_simp [ne_of_gt hwi]
    exact heq.le

theorem fourier_low_part_pointwise_bound (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (v : Torus d L → ℂ), neutral v →
        ∀ x : Torus d L,
          ∃ S : Finset (Torus d L),
            S = Finset.univ.filter (fun k =>
              1 ≤ torusDistance (0 : Torus d L) k ∧
                torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊) ∧
            ‖fourierBandPart S v x‖ ^ 2 ≤ C * a * gradientEnergy v := by
  obtain ⟨C, hC, hInv⟩ := low_frequency_inverse_sum_bound hd
  refine ⟨C, hC, fun L _ hL a ha0 ha1 v hv x => ?_⟩
  let R : ℕ := ⌊a * (L : ℝ)⌋₊
  let dist : Torus d L → ℕ := fun k => torusDistance (0 : Torus d L) k
  let lam : Torus d L → ℝ := fun k => laplacianSymbol (gridAngle k)
  let S : Finset (Torus d L) := Finset.univ.filter (fun k => 1 ≤ dist k ∧ dist k ≤ R)
  have hS : S = Finset.univ.filter (fun k =>
      1 ≤ torusDistance (0 : Torus d L) k ∧
        torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊) := by
    ext k
    simp [S, dist, R]
  have hInvAvg : gridAvgReal (fun k => if k ∈ S then (lam k)⁻¹ else 0) ≤ C * a := by
    simpa [S, lam, dist, R] using hInv L hL a ha0 ha1
  have hInvAvg' : (Fintype.card (Torus d L) : ℝ)⁻¹ *
      ∑ k ∈ S, (lam k)⁻¹ ≤ C * a := by
    simpa [gridAvgReal] using hInvAvg
  have hLamPos : ∀ k ∈ S, 0 < lam k := by
    intro k hk
    have hdist := (Finset.mem_filter.mp hk).2.1
    have hdistR : (1 : ℝ) ≤ (dist k : ℝ) := by exact_mod_cast hdist
    have hbound := laplacianSymbol_lower_distance hd hL k
    have hcoeff : 0 < 16 / ((d : ℝ) * (L : ℝ) ^ 2) := by positivity
    have : 0 < (16 / ((d : ℝ) * (L : ℝ) ^ 2)) * (dist k : ℝ) ^ 2 := by
      positivity
    exact lt_of_lt_of_le this (by simpa [lam, dist] using hbound)
  have hCS : (∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖) ^ 2 ≤
      (∑ k ∈ S, (lam k)⁻¹) *
        ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 :=
    weighted_cauchy_finset S lam (AndersonAC.S3.fourier v) hLamPos
  have hsumNorm :
      ‖∑ k : Torus d L,
          (if k ∈ S then AndersonAC.S3.character k x *
            AndersonAC.S3.fourier v k else 0)‖ ≤
        ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖ := by
    calc
      ‖∑ k : Torus d L,
          (if k ∈ S then AndersonAC.S3.character k x *
            AndersonAC.S3.fourier v k else 0)‖ ≤
        ∑ k, ‖if k ∈ S then AndersonAC.S3.character k x *
            AndersonAC.S3.fourier v k else 0‖ := norm_sum_le _ _
      _ = ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖ := by
        calc
          (∑ k, ‖if k ∈ S then AndersonAC.S3.character k x *
              AndersonAC.S3.fourier v k else 0‖) =
              ∑ k, (if k ∈ S then ‖AndersonAC.S3.fourier v k‖ else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                by_cases hk : k ∈ S <;> simp [hk, norm_mul,
                  AndersonAC.S3.character_norm_eq]
          _ = ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖ := by
                simpa using (Finset.sum_ite_mem_eq (s := S)
                  (f := fun k : Torus d L => ‖AndersonAC.S3.fourier v k‖))
  have hNpos : 0 < (Fintype.card (Torus d L) : ℝ)⁻¹ := by positivity
  have hNnorm :
      ‖((Fintype.card (Torus d L) : ℂ)⁻¹)‖ =
        (Fintype.card (Torus d L) : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_natCast]
  have hpartNorm : ‖fourierBandPart S v x‖ ≤
      (Fintype.card (Torus d L) : ℝ)⁻¹ *
        ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖ := by
    unfold fourierBandPart AndersonAC.S3.gridAvg
    rw [norm_mul, hNnorm]
    exact mul_le_mul_of_nonneg_left hsumNorm (le_of_lt hNpos)
  have hpartSq : ‖fourierBandPart S v x‖ ^ 2 ≤
      ((Fintype.card (Torus d L) : ℝ)⁻¹ *
        ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) hpartNorm
  have hsubsetEnergy :
      (Fintype.card (Torus d L) : ℝ)⁻¹ *
        ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 ≤
          gradientEnergy v := by
    rw [fourier_gradientEnergy hL v]
    unfold gridAvgReal
    have hsum : (∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
        ∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 := by
      calc
        (∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) =
            ∑ k, (if k ∈ S then lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 else 0) := by
              symm
              exact Finset.sum_ite_mem_eq (s := S)
                (f := fun k : Torus d L => lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2)
        _ ≤ ∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro k _
              by_cases hk : k ∈ S
              · simp [hk]
              · simp [hk]
                have hLamNonneg : 0 ≤ lam k := by
                  dsimp [lam, laplacianSymbol]
                  exact mul_nonneg (by norm_num)
                    (Finset.sum_nonneg (fun j _ => sq_nonneg _))
                exact mul_nonneg hLamNonneg (sq_nonneg _)
    simpa [lam] using mul_le_mul_of_nonneg_left hsum (by positivity)
  have hNenergy : 0 ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ *
      ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 := by
    apply mul_nonneg (le_of_lt hNpos)
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (le_of_lt (hLamPos k hk)) (sq_nonneg _)
  have hCaNonneg : 0 ≤ C * a := mul_nonneg hC.le ha0.le
  have hlowprod :
      ((Fintype.card (Torus d L) : ℝ)⁻¹ * ∑ k ∈ S, (lam k)⁻¹) *
        ((Fintype.card (Torus d L) : ℝ)⁻¹ *
          ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
          C * a * gradientEnergy v := by
    calc
      _ ≤ (C * a) *
            ((Fintype.card (Torus d L) : ℝ)⁻¹ *
              ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hInvAvg' hNenergy
      _ ≤ (C * a) * gradientEnergy v :=
              mul_le_mul_of_nonneg_left hsubsetEnergy hCaNonneg
  refine ⟨S, hS, ?_⟩
  calc
    ‖fourierBandPart S v x‖ ^ 2 ≤
        ((Fintype.card (Torus d L) : ℝ)⁻¹ *
          ∑ k ∈ S, ‖AndersonAC.S3.fourier v k‖) ^ 2 := hpartSq
    _ ≤ ((Fintype.card (Torus d L) : ℝ)⁻¹) ^ 2 *
          ((∑ k ∈ S, (lam k)⁻¹) *
            (∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = ((Fintype.card (Torus d L) : ℝ)⁻¹ *
          ∑ k ∈ S, (lam k)⁻¹) *
          ((Fintype.card (Torus d L) : ℝ)⁻¹ *
            ∑ k ∈ S, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by ring
    _ ≤ C * a * gradientEnergy v := hlowprod

theorem fourier_high_part_energy_bound (hd : 3 ≤ d) :
    ∀ (L : ℕ) [NeZero L], 4 ≤ L → ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ (v : Torus d L → ℂ), neutral v →
        ∃ S : Finset (Torus d L),
          S = Finset.univ.filter (fun k =>
            1 ≤ torusDistance (0 : Torus d L) k ∧
              torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊) ∧
          normSq (fourierBandComplement S v) ≤
            (d : ℝ) / (16 * a ^ 2) * gradientEnergy v := by
  intro L inst hL a ha0 ha1 v hv
  let R : ℕ := ⌊a * (L : ℝ)⌋₊
  let dist : Torus d L → ℕ := fun k => torusDistance (0 : Torus d L) k
  let lam : Torus d L → ℝ := fun k => laplacianSymbol (gridAngle k)
  let S : Finset (Torus d L) := Finset.univ.filter (fun k => 1 ≤ dist k ∧ dist k ≤ R)
  have hS : S = Finset.univ.filter (fun k =>
      1 ≤ torusDistance (0 : Torus d L) k ∧
        torusDistance (0 : Torus d L) k ≤ ⌊a * (L : ℝ)⌋₊) := by
    ext k
    simp [S, dist, R]
  have hRnonneg : 0 ≤ a * (L : ℝ) := by positivity
  have hzero : AndersonAC.S3.fourier v 0 = 0 := by
    rw [fourier_zero_eq_sum]
    exact hv
  let coeff : Torus d L → ℂ := fun k => if k ∈ S then 0 else AndersonAC.S3.fourier v k
  have hHighEq : fourierBandComplement S v = AndersonAC.S3.synthesis coeff := by
    funext x
    unfold fourierBandComplement AndersonAC.S3.synthesis AndersonAC.S3.gridAvg
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ S <;> simp [coeff, hk]
  have hFourierCoeff : ∀ k, AndersonAC.S3.fourier (fourierBandComplement S v) k = coeff k := by
    intro k
    rw [hHighEq, AndersonAC.S3.fourier_synthesis]
  have hmode : ∀ k : Torus d L,
      ‖coeff k‖ ^ 2 ≤ (d : ℝ) / (16 * a ^ 2) *
        (lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    intro k
    by_cases hk : k ∈ S
    · have hLamNonneg : 0 ≤ lam k := by
        dsimp [lam, laplacianSymbol]
        exact mul_nonneg (by norm_num)
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      simp [coeff, hk]
      positivity
    · by_cases hdist0 : dist k = 0
      · have hk0 : k = 0 := (torusDistance_zero_iff k).mp (by simpa [dist] using hdist0)
        subst k
        simp [coeff, S, dist, hzero, lam, laplacianSymbol, gridAngle]
      · have hdistpos : 0 < dist k := Nat.pos_of_ne_zero hdist0
        have hdistR : R < dist k := by
          by_contra hn
          have hle : dist k ≤ R := Nat.le_of_not_gt hn
          have hone : 1 ≤ dist k := by omega
          apply hk
          simp [S, dist, hone, hle]
        have hdistA : a * (L : ℝ) < (dist k : ℝ) :=
          (Nat.floor_lt hRnonneg).mp hdistR
        have hdistSq : (a * (L : ℝ)) ^ 2 ≤ (dist k : ℝ) ^ 2 :=
          by simpa [pow_two] using mul_self_le_mul_self (by positivity) hdistA.le
        have hbound := laplacianSymbol_lower_distance hd hL k
        have hscale : 16 * a ^ 2 / (d : ℝ) ≤ lam k := by
          have hmul := mul_le_mul_of_nonneg_left hdistSq
            (show 0 ≤ 16 / ((d : ℝ) * (L : ℝ) ^ 2) by positivity)
          have heq : 16 / ((d : ℝ) * (L : ℝ) ^ 2) *
              (a * (L : ℝ)) ^ 2 = 16 * a ^ 2 / (d : ℝ) := by
            field_simp
          rw [heq] at hmul
          exact hmul.trans (by simpa [dist, lam] using hbound)
        have hcoef : 1 ≤ (d : ℝ) / (16 * a ^ 2) * lam k := by
          have hmul := mul_le_mul_of_nonneg_left hscale
            (show 0 ≤ (d : ℝ) / (16 * a ^ 2) by positivity)
          have heq : (d : ℝ) / (16 * a ^ 2) * (16 * a ^ 2 / (d : ℝ)) = 1 := by
            field_simp
          nlinarith [hmul, heq]
        have hmul := mul_le_mul_of_nonneg_right hcoef
          (sq_nonneg ‖AndersonAC.S3.fourier v k‖)
        have hmode : ‖AndersonAC.S3.fourier v k‖ ^ 2 ≤
            (d : ℝ) / (16 * a ^ 2) *
              (lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
          calc
            ‖AndersonAC.S3.fourier v k‖ ^ 2 =
                1 * ‖AndersonAC.S3.fourier v k‖ ^ 2 := by ring
            _ ≤ ((d : ℝ) / (16 * a ^ 2) * lam k) *
                  ‖AndersonAC.S3.fourier v k‖ ^ 2 := hmul
            _ = _ := by ring
        simpa [coeff, hk] using hmode
  have hsumMode : (∑ k, ‖coeff k‖ ^ 2) ≤
      (d : ℝ) / (16 * a ^ 2) *
        (∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    calc
      (∑ k, ‖coeff k‖ ^ 2) ≤
          ∑ k, (d : ℝ) / (16 * a ^ 2) *
            (lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
              Finset.sum_le_sum (fun k _ => hmode k)
      _ = (d : ℝ) / (16 * a ^ 2) *
            ∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2 := by
              rw [← Finset.mul_sum]
  have hAvg : gridAvgReal (fun k => ‖coeff k‖ ^ 2) ≤
      (d : ℝ) / (16 * a ^ 2) * gridAvgReal (fun k =>
        lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    unfold gridAvgReal
    have hN : 0 ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card (Torus d L) : ℝ)⁻¹ * ∑ k, ‖coeff k‖ ^ 2
        ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ *
            ((d : ℝ) / (16 * a ^ 2) *
              ∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hsumMode hN
      _ = (d : ℝ) / (16 * a ^ 2) *
            ((Fintype.card (Torus d L) : ℝ)⁻¹ *
              ∑ k, lam k * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by ring
  have hParseval : normSq (fourierBandComplement S v) =
      gridAvgReal (fun k => ‖coeff k‖ ^ 2) := by
    rw [AndersonAC.S3.parseval]
    simp_rw [hFourierCoeff]
  refine ⟨S, hS, ?_⟩
  calc
    normSq (fourierBandComplement S v) = gridAvgReal (fun k => ‖coeff k‖ ^ 2) := hParseval
    _ ≤ (d : ℝ) / (16 * a ^ 2) * gradientEnergy v := by
      rw [fourier_gradientEnergy hL v]
      simpa [lam] using hAvg

end AndersonAC.AgentS3
