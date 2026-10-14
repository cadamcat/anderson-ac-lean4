import AndersonAC.S3.CirculantStatements
import AndersonAC.S3.GridCount
import AndersonAC.S3.Dispersion

noncomputable section
open scoped BigOperators
open scoped Matrix

namespace AndersonAC.S3

variable {d L : ℕ} [NeZero L]

lemma angle1_signed (z : ZMod L) :
    ∃ m : ℤ, (m : ZMod L) = z ∧ angle1 L z = 2 * Real.pi * m / L := by
  have hzlt := z.val_lt
  have hcast : ((z.val : ℤ) : ZMod L) = z := by
    exact_mod_cast ZMod.natCast_zmod_val z
  by_cases h : 2 * z.val < L
  · refine ⟨z.val, hcast, ?_⟩
    have hi := angle1_intCast (L := L) (z.val : ℤ) (by omega) (by exact_mod_cast h)
    rw [hcast] at hi
    exact hi
  · refine ⟨(z.val : ℤ) - L, ?_, ?_⟩
    · calc
        (((z.val : ℤ) - L : ℤ) : ZMod L) =
            ((z.val : ℤ) : ZMod L) - (L : ℤ) := by push_cast; rfl
        _ = z := by rw [hcast]; simp
    · have hi := angle1_intCast (L := L) ((z.val : ℤ) - L) (by omega) (by omega)
      have hm : (((z.val : ℤ) - L : ℤ) : ZMod L) = z := by
        calc
          (((z.val : ℤ) - L : ℤ) : ZMod L) =
              ((z.val : ℤ) : ZMod L) - (L : ℤ) := by push_cast; rfl
          _ = z := by rw [hcast]; simp
      rw [hm] at hi
      exact hi

lemma stdAddChar_eq_exp_angle (z : ZMod L) :
    ZMod.stdAddChar z = Complex.exp (Complex.I * (angle1 L z : ℂ)) := by
  obtain ⟨m, hm, hangle⟩ := angle1_signed (L := L) z
  calc
    ZMod.stdAddChar z = ZMod.stdAddChar (m : ZMod L) := by rw [hm]
    _ = Complex.exp (2 * Real.pi * Complex.I * m / L) := ZMod.stdAddChar_coe m
    _ = Complex.exp (Complex.I * (angle1 L z : ℂ)) := by
      rw [hangle]
      congr 1
      push_cast
      ring

lemma exp_angle_pow (z : ZMod L) (n : ℕ) :
    Complex.exp (Complex.I * ((angle1 L z : ℂ) * n)) =
      (ZMod.stdAddChar z) ^ n := by
  rw [stdAddChar_eq_exp_angle]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma stdAddChar_mul_val (k x : ZMod L) :
    ZMod.stdAddChar (k * x) = (ZMod.stdAddChar k) ^ x.val := by
  have hx : (x.val : ZMod L) = x := ZMod.natCast_zmod_val x
  rw [← hx, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [nsmul_eq_mul, mul_comm]

lemma character_eq_prod_stdAddChar (k x : Torus d L) :
    character k x = ∏ j, ZMod.stdAddChar (k j * x j) := by
  unfold character
  have hphase : Complex.I * (∑ j, gridAngle k j * ((x j).val : ℝ)) =
      ∑ j, Complex.I * ((gridAngle k j * ((x j).val : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
  rw [hphase, Complex.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [show gridAngle k j = angle1 L (k j) from gridAngle_apply _ _]
  push_cast
  rw [exp_angle_pow]
  exact (stdAddChar_mul_val (k j) (x j)).symm

lemma character_norm (k x : Torus d L) : ‖character k x‖ = 1 := by
  rw [character_eq_prod_stdAddChar]
  simp [AddChar.norm_apply]

def characterAddChar (k : Torus d L) : AddChar (Torus d L) ℂ where
  toFun := character k
  map_zero_eq_one' := by
    rw [character_eq_prod_stdAddChar]
    simp
  map_add_eq_mul' x y := by
    rw [character_eq_prod_stdAddChar, character_eq_prod_stdAddChar,
      character_eq_prod_stdAddChar]
    simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul]
    rw [← Finset.prod_mul_distrib]

lemma character_basisStep (k : Torus d L) (j : Fin d) :
    character k (basisStep j) = ZMod.stdAddChar (k j) := by
  rw [character_eq_prod_stdAddChar]
  calc
    (∏ i : Fin d, ZMod.stdAddChar (k i * basisStep j i)) =
        ZMod.stdAddChar (k j * basisStep j j) := by
      classical
      exact Finset.prod_eq_single (s := Finset.univ)
        (f := fun i => ZMod.stdAddChar (k i * basisStep j i)) j
        (by
          intro i hi hij
          simp [basisStep, hij])
        (by simp)
    _ = ZMod.stdAddChar (k j) := by simp [basisStep]

theorem characterAddChar_injective : Function.Injective (characterAddChar (d := d) (L := L)) := by
  intro k l h
  apply funext
  intro j
  have hv := congrArg (fun χ : AddChar (Torus d L) ℂ => χ (basisStep j)) h
  change character k (basisStep j) = character l (basisStep j) at hv
  rw [character_basisStep, character_basisStep] at hv
  have hchar : ZMod.stdAddChar (k j) = ZMod.stdAddChar (l j) := hv
  exact ZMod.injective_stdAddChar hchar

lemma character_inner (k l : Torus d L) :
    ⟪(characterAddChar k : Torus d L → ℂ),
      (characterAddChar l : Torus d L → ℂ)⟫ₙ_[ℂ] = if k = l then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole (characterAddChar k) (characterAddChar l)
  have heq : characterAddChar k = characterAddChar l ↔ k = l :=
    characterAddChar_injective.eq_iff
  simpa only [heq] using h

lemma character_sum_orthog (k l : Torus d L) :
    ∑ x, star (character k x) * character l x =
      if k = l then (Fintype.card (Torus d L) : ℂ) else 0 := by
  have h := character_inner (d := d) (L := L) k l
  have hcard : 0 < Fintype.card (Torus d L) :=
    Fintype.card_pos_iff.mpr ⟨(0 : Torus d L)⟩
  have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hsumdiv :
      (∑ x, character l x * star (character k x)) /
          (Fintype.card (Torus d L) : ℂ) = if k = l then 1 else 0 := by
    simpa [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
      RCLike.inner_apply, characterAddChar] using h
  have hnorm : (Fintype.card (Torus d L) : ℂ)⁻¹ *
      (∑ x, star (character k x) * character l x) = if k = l then 1 else 0 := by
    calc
      (Fintype.card (Torus d L) : ℂ)⁻¹ *
          (∑ x, star (character k x) * character l x) =
        (∑ x, character l x * star (character k x)) /
            (Fintype.card (Torus d L) : ℂ) := by
          rw [div_eq_mul_inv]
          calc
            (Fintype.card (Torus d L) : ℂ)⁻¹ *
                (∑ x, star (character k x) * character l x) =
              (∑ x, star (character k x) * character l x) *
                (Fintype.card (Torus d L) : ℂ)⁻¹ := mul_comm _ _
            _ = (∑ x, character l x * star (character k x)) *
                (Fintype.card (Torus d L) : ℂ)⁻¹ := by
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              ring
      _ = _ := hsumdiv
  have hmul := congrArg (fun q : ℂ => (Fintype.card (Torus d L) : ℂ) * q) hnorm
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul] at hmul
  simpa only [mul_ite, mul_one, mul_zero] using hmul

lemma character_swap (k x : Torus d L) : character k x = character x k := by
  rw [character_eq_prod_stdAddChar, character_eq_prod_stdAddChar]
  apply Finset.prod_congr rfl
  intro j hj
  rw [mul_comm]

lemma character_sum_k_orthog (x y : Torus d L) :
    ∑ k, character k x * star (character k y) =
      if x = y then (Fintype.card (Torus d L) : ℂ) else 0 := by
  calc
    ∑ k, character k x * star (character k y) =
        ∑ k, star (character y k) * character x k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [character_swap k x, character_swap k y]
      ring
    _ = if y = x then (Fintype.card (Torus d L) : ℂ) else 0 := character_sum_orthog y x
    _ = _ := by simp [eq_comm]

lemma sum_fourier_mul_character (f : Torus d L → ℂ) (x : Torus d L) :
    ∑ k, fourier f k * character k x =
      ∑ y, f y * (∑ k, star (character k y) * character k x) := by
  unfold fourier
  calc
    ∑ k, (∑ y, f y * star (character k y)) * character k x =
        ∑ k, ∑ y, (f y * star (character k y)) * character k x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
    _ = ∑ y, ∑ k, (f y * star (character k y)) * character k x := Finset.sum_comm
    _ = ∑ y, f y * (∑ k, star (character k y) * character k x) := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        ∑ k, (f y * star (character k y)) * character k x =
            ∑ k, f y * (star (character k y) * character k x) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = f y * (∑ k, star (character k y) * character k x) :=
          (Finset.mul_sum ..).symm

lemma fourier_inverse_point (f : Torus d L → ℂ) (x : Torus d L) :
    f x = gridAvg (fun k => fourier f k * character k x) := by
  have hcard : 0 < Fintype.card (Torus d L) := Fintype.card_pos_iff.mpr ⟨(0 : Torus d L)⟩
  have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  unfold gridAvg
  rw [sum_fourier_mul_character]
  have heval : ∑ y, f y * (∑ k, star (character k y) * character k x) =
      f x * (Fintype.card (Torus d L) : ℂ) := by
    calc
      ∑ y, f y * (∑ k, star (character k y) * character k x) =
          ∑ y, f y * (if y = x then (Fintype.card (Torus d L) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        calc
          ∑ k, star (character k y) * character k x =
              ∑ k, character k x * star (character k y) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = if x = y then (Fintype.card (Torus d L) : ℂ) else 0 :=
            character_sum_k_orthog x y
          _ = _ := by simp [eq_comm]
      _ = f x * (Fintype.card (Torus d L) : ℂ) := by simp
  rw [heval]
  field_simp [hN]

lemma star_fourier (f : Torus d L → ℂ) (k : Torus d L) :
    star (fourier f k) = ∑ x, star (f x) * character k x := by
  unfold fourier
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [map_mul]

lemma fourier_inner_eq_gridAvg (f g : Torus d L → ℂ) :
    ∑ x, star (f x) * g x = gridAvg (fun k => star (fourier f k) * fourier g k) := by
  calc
    ∑ x, star (f x) * g x =
        ∑ x, star (f x) * gridAvg (fun k => fourier g k * character k x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [fourier_inverse_point g x]
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ x, ∑ k, star (f x) * (fourier g k * character k x) := by
      unfold gridAvg
      calc
        ∑ x, star (f x) *
            ((Fintype.card (Torus d L) : ℂ)⁻¹ *
              ∑ k, fourier g k * character k x) =
          ∑ x, (Fintype.card (Torus d L) : ℂ)⁻¹ *
            (star (f x) * ∑ k, fourier g k * character k x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
            ∑ x, star (f x) * ∑ k, fourier g k * character k x :=
          (Finset.mul_sum ..).symm
        _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
            ∑ x, ∑ k, star (f x) * (fourier g k * character k x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.mul_sum ..
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, ∑ x, star (f x) * (fourier g k * character k x) := by
      congr 1
      exact Finset.sum_comm
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, fourier g k * (∑ x, star (f x) * character k x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ x, star (f x) * (fourier g k * character k x) =
            ∑ x, fourier g k * (star (f x) * character k x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = fourier g k * (∑ x, star (f x) * character k x) :=
          (Finset.mul_sum ..).symm
    _ = gridAvg (fun k => star (fourier f k) * fourier g k) := by
      unfold gridAvg
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← star_fourier]
      ring

lemma fourier_parseval (f : Torus d L → ℂ) :
    normSq f = gridAvgReal (fun k => ‖fourier f k‖ ^ 2) := by
  have h := fourier_inner_eq_gridAvg f f
  have hcast : (normSq f : ℂ) =
      (gridAvgReal (fun k => ‖fourier f k‖ ^ 2) : ℂ) := by
    simpa [normSq, gridAvg, gridAvgReal, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq] using h
  exact Complex.ofReal_injective hcast

lemma fourier_injective : Function.Injective (fourier (d := d) (L := L)) := by
  intro f g h
  funext x
  calc
    f x = gridAvg (fun k => fourier f k * character k x) := fourier_inverse_point f x
    _ = gridAvg (fun k => fourier g k * character k x) := by
      congr 1
      funext k
      rw [congrFun h k]
    _ = g x := (fourier_inverse_point g x).symm

lemma fourier_add (f g : Torus d L → ℂ) (k : Torus d L) :
    fourier (f + g) k = fourier f k + fourier g k := by
  unfold fourier
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma fourier_sub (f g : Torus d L → ℂ) (k : Torus d L) :
    fourier (f - g) k = fourier f k - fourier g k := by
  unfold fourier
  simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma fourier_smul (c : ℂ) (f : Torus d L → ℂ) (k : Torus d L) :
    fourier (c • f) k = c * fourier f k := by
  unfold fourier
  calc
    ∑ x, (c • f) x * star (character k x) =
        ∑ x, c * (f x * star (character k x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = c * ∑ x, f x * star (character k x) := (Finset.mul_sum ..).symm

def deltaZero : Torus d L → ℂ := fun x => if x = 0 then 1 else 0

lemma fourier_deltaZero (k : Torus d L) : fourier deltaZero k = 1 := by
  unfold fourier deltaZero
  simp [character_eq_prod_stdAddChar]

lemma circulant_deltaZero (d L : ℕ) [NeZero L] : circulant (deltaZero (d := d) (L := L)) =
    (1 : Matrix (Torus d L) (Torus d L) ℂ) := by
  ext x y
  simp [circulant, deltaZero, Matrix.one_apply, sub_eq_zero]

def inverseFourier (s : Torus d L → ℂ) : Torus d L → ℂ :=
  fun x => gridAvg (fun k => s k * character k x)

lemma fourier_inverseFourier (s : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (inverseFourier s) ζ = s ζ := by
  have hcard : 0 < Fintype.card (Torus d L) := Fintype.card_pos_iff.mpr ⟨(0 : Torus d L)⟩
  have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  unfold fourier inverseFourier
  calc
    ∑ x, ((Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, s k * character k x) * star (character ζ x) =
      (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ x, ∑ k, s k * character k x * star (character ζ x) := by
      calc
        ∑ x, ((Fintype.card (Torus d L) : ℂ)⁻¹ *
            ∑ k, s k * character k x) * star (character ζ x) =
          ∑ x, (Fintype.card (Torus d L) : ℂ)⁻¹ *
            ((∑ k, s k * character k x) * star (character ζ x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
            ∑ x, (∑ k, s k * character k x) * star (character ζ x) :=
          (Finset.mul_sum ..).symm
        _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
            ∑ x, ∑ k, s k * character k x * star (character ζ x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.sum_mul ..
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, ∑ x, s k * character k x * star (character ζ x) := by
      congr 1
      exact Finset.sum_comm
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, s k * (∑ x, character k x * star (character ζ x)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ x, s k * character k x * star (character ζ x) =
            ∑ x, s k * (character k x * star (character ζ x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = s k * (∑ x, character k x * star (character ζ x)) :=
          (Finset.mul_sum ..).symm
    _ = (Fintype.card (Torus d L) : ℂ)⁻¹ * (s ζ * (Fintype.card (Torus d L) : ℂ)) := by
      congr 1
      calc
        ∑ k, s k * (∑ x, character k x * star (character ζ x)) =
            ∑ k, s k * (if k = ζ then (Fintype.card (Torus d L) : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          calc
            ∑ x, character k x * star (character ζ x) =
                ∑ x, star (character ζ x) * character k x := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = if ζ = k then (Fintype.card (Torus d L) : ℂ) else 0 :=
              character_sum_orthog ζ k
            _ = _ := by simp [eq_comm]
        _ = s ζ * (Fintype.card (Torus d L) : ℂ) := by simp
    _ = s ζ := by field_simp [hN]

lemma character_add_right (k x y : Torus d L) :
    character k (x + y) = character k x * character k y :=
  AddChar.map_add_eq_mul (characterAddChar k) x y

lemma character_add_left (k l x : Torus d L) :
    character (k + l) x = character k x * character l x := by
  rw [character_swap (k + l) x, character_swap k x, character_swap l x]
  exact AddChar.map_add_eq_mul (characterAddChar x) k l

lemma character_zero_left (x : Torus d L) : character 0 x = 1 := by
  rw [character_eq_prod_stdAddChar]
  simp

lemma character_star (k x : Torus d L) :
    star (character k x) = character k (-x) := by
  have hn := character_norm k x
  calc
    star (character k x) = (character k x)⁻¹ := (RCLike.inv_eq_conj hn).symm
    _ = character k (-x) := by
      symm
      exact AddChar.map_neg_eq_inv (characterAddChar k) x

lemma fourier_conj_reverse (m : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (fun x => star (m (-x))) ζ = star (fourier m ζ) := by
  unfold fourier
  rw [star_sum]
  symm
  refine Fintype.sum_equiv (Equiv.neg _) _ _ ?_
  intro x
  rw [character_star]
  simp

lemma circulant_hermitian_of_real_symbol (m : Torus d L → ℂ)
    (hreal : ∀ ζ, (fourier m ζ).im = 0) :
    (Matrix.circulant m).conjTranspose = Matrix.circulant m := by
  have hkernel : (fun x => star (m (-x))) = m := by
    apply fourier_injective
    funext ζ
    rw [fourier_conj_reverse]
    have hz : star (fourier m ζ) = fourier m ζ := by
      apply Complex.ext <;> simp [hreal ζ]
    exact hz
  calc
    (Matrix.circulant m).conjTranspose =
        Matrix.circulant (fun x => star (m (-x))) := by
      have hfun : star (fun x : Torus d L => m (-x)) =
          (fun x => star (m (-x))) := by
        funext x
        rfl
      rw [← hfun]
      exact Matrix.conjTranspose_circulant m
    _ = Matrix.circulant m := congrArg Matrix.circulant hkernel

lemma fourier_translate (m : Torus d L → ℂ) (ζ y : Torus d L) :
    ∑ x, m (x - y) * star (character ζ x) =
      star (character ζ y) * fourier m ζ := by
  calc
    ∑ x, m (x - y) * star (character ζ x) =
        ∑ x, m x * star (character ζ (x + y)) := by
      symm
      refine Fintype.sum_equiv (Equiv.addRight y) _ _ ?_
      intro x
      simp [Equiv.coe_addRight]
    _ = ∑ x, m x * (star (character ζ x) * star (character ζ y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [character_add_right]
      rw [star_mul]
      ring
    _ = star (character ζ y) * fourier m ζ := by
      calc
        ∑ x, m x * (star (character ζ x) * star (character ζ y)) =
            ∑ x, star (character ζ y) * (m x * star (character ζ x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = star (character ζ y) * fourier m ζ := by
          unfold fourier
          rw [Finset.mul_sum]

lemma fourier_mulVec_circulant (m m' : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (Matrix.circulant m *ᵥ m') ζ = fourier m ζ * fourier m' ζ := by
  classical
  simp only [fourier, Matrix.mulVec, dotProduct, Matrix.circulant_apply]
  calc
    ∑ x, (∑ y, m (x - y) * m' y) * star (character ζ x) =
        ∑ y, m' y * (∑ x, m (x - y) * star (character ζ x)) := by
      calc
        ∑ x, (∑ y, m (x - y) * m' y) * star (character ζ x) =
            ∑ x, ∑ y, (m (x - y) * m' y) * star (character ζ x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
        _ = ∑ y, ∑ x, (m (x - y) * m' y) * star (character ζ x) := Finset.sum_comm
        _ = ∑ y, m' y * (∑ x, m (x - y) * star (character ζ x)) := by
          apply Finset.sum_congr rfl
          intro y hy
          calc
            ∑ x, (m (x - y) * m' y) * star (character ζ x) =
                ∑ x, m' y * (m (x - y) * star (character ζ x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = m' y * (∑ x, m (x - y) * star (character ζ x)) :=
              (Finset.mul_sum ..).symm
    _ = fourier m ζ * fourier m' ζ := by
      simp_rw [fourier_translate]
      unfold fourier
      calc
        ∑ y, m' y * (star (character ζ y) * ∑ x, m x * star (character ζ x)) =
            (∑ y, m' y * star (character ζ y)) *
              (∑ x, m x * star (character ζ x)) := by
          calc
            ∑ y, m' y * (star (character ζ y) * ∑ x, m x * star (character ζ x)) =
                ∑ y, (m' y * star (character ζ y)) *
                  (∑ x, m x * star (character ζ x)) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
            _ = (∑ y, m' y * star (character ζ y)) *
                  (∑ x, m x * star (character ζ x)) := (Finset.sum_mul ..).symm
        _ = _ := by ring

lemma fourier_twist (f : Torus d L → ℂ) (ζ k : Torus d L) :
    fourier (fun x => f x * star (character ζ x)) k = fourier f (k + ζ) := by
  unfold fourier
  apply Finset.sum_congr rfl
  intro x hx
  calc
    f x * star (character ζ x) * star (character k x) =
        f x * star (character (k + ζ) x) := by
      rw [character_add_left]
      simp [star_mul, mul_assoc, mul_comm, mul_left_comm]
    _ = f x * star (character (k + ζ) x) := rfl

lemma fourier_normSq_inverseFourier (s : Torus d L → ℂ) (ζ : Torus d L) :
    fourier (fun x => ((‖inverseFourier s x‖ ^ 2 : ℝ) : ℂ)) ζ =
      gridAvg (fun k => star (s k) * s (k + ζ)) := by
  let g : Torus d L → ℂ := inverseFourier s
  let q : Torus d L → ℂ := fun x => g x * star (character ζ x)
  have hnorm (x : Torus d L) :
      ((‖g x‖ ^ 2 : ℝ) : ℂ) = star (g x) * g x := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  have hpair := fourier_inner_eq_gridAvg g q
  have hleft : fourier (fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ)) ζ =
      ∑ x, star (g x) * q x := by
    unfold fourier q
    apply Finset.sum_congr rfl
    intro x hx
    change ((‖g x‖ ^ 2 : ℝ) : ℂ) * star (character ζ x) = _
    rw [hnorm x]
    ring
  have hshift : ∀ k, fourier q k = fourier g (k + ζ) := by
    intro k
    exact fourier_twist g ζ k
  have hFg : ∀ k, fourier g k = s k := by
    intro k
    exact fourier_inverseFourier s k
  calc
    fourier (fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ)) ζ =
        gridAvg (fun k => star (fourier g k) * fourier q k) := hleft.trans hpair
    _ = gridAvg (fun k => star (s k) * s (k + ζ)) := by
      congr 1
      funext k
      rw [hFg k, hshift k, hFg]

def deltaAt (a : Torus d L) : Torus d L → ℂ := fun x => if x = a then 1 else 0

lemma fourier_deltaAt (a ζ : Torus d L) :
    fourier (deltaAt a) ζ = star (character ζ a) := by
  unfold fourier deltaAt
  simp

lemma fourier_fintype_sum {ι : Type*} [Fintype ι] (f : ι → Torus d L → ℂ)
    (ζ : Torus d L) : fourier (fun x => ∑ i, f i x) ζ = ∑ i, fourier (f i) ζ := by
  unfold fourier
  calc
    ∑ x, (∑ i, f i x) * star (character ζ x) =
        ∑ x, ∑ i, f i x * star (character ζ x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ x, f i x * star (character ζ x) := by
      rw [Finset.sum_comm]

lemma fourier_sum_functions {ι : Type*} [Fintype ι] (f : ι → Torus d L → ℂ)
    (ζ : Torus d L) : fourier (∑ i, f i) ζ = ∑ i, fourier (f i) ζ := by
  have hfun : (∑ i, f i) = (fun x => ∑ i, f i x) := by
    funext x
    exact Fintype.sum_apply x f
  rw [hfun]
  exact fourier_fintype_sum f ζ

lemma re_star_mul_mul (a b : ℂ) :
    (star b * (a * b)).re = a.re * ‖b‖ ^ 2 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq]
  ring

lemma re_gridAvg_star_mul_mul (a b : Torus d L → ℂ) :
    (gridAvg (fun ζ => star (b ζ) * (a ζ * b ζ))).re =
      gridAvgReal (fun ζ => (a ζ).re * ‖b ζ‖ ^ 2) := by
  have hsum : (∑ ζ, (star (b ζ) * (a ζ * b ζ))).re =
      ∑ ζ, (a ζ).re * ‖b ζ‖ ^ 2 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ζ hζ
    exact re_star_mul_mul (a ζ) (b ζ)
  have hinv : (Fintype.card (Torus d L) : ℂ)⁻¹ =
      Complex.ofReal ((Fintype.card (Torus d L) : ℝ)⁻¹) := by
    exact (Complex.ofReal_inv (Fintype.card (Torus d L) : ℝ)).symm
  have hre : ((Fintype.card (Torus d L) : ℂ)⁻¹).re =
      (Fintype.card (Torus d L) : ℝ)⁻¹ := by
    calc
      ((Fintype.card (Torus d L) : ℂ)⁻¹).re =
          (Complex.ofReal ((Fintype.card (Torus d L) : ℝ)⁻¹)).re := congrArg Complex.re hinv
      _ = (Fintype.card (Torus d L) : ℝ)⁻¹ := Complex.ofReal_re _
  have him : ((Fintype.card (Torus d L) : ℂ)⁻¹).im = 0 := by
    calc
      ((Fintype.card (Torus d L) : ℂ)⁻¹).im =
          (Complex.ofReal ((Fintype.card (Torus d L) : ℝ)⁻¹)).im := congrArg Complex.im hinv
      _ = 0 := Complex.ofReal_im _
  unfold gridAvg gridAvgReal
  rw [Complex.mul_re, hre, him, zero_mul, sub_zero, hsum]

lemma circulant_form_diagonalized (m y : Torus d L → ℂ) :
    form (circulant m) y =
      gridAvgReal (fun ζ => (fourier m ζ).re * ‖fourier y ζ‖ ^ 2) := by
  have hdiag : fourier ((circulant m).mulVec y) =
      fun ζ => fourier m ζ * fourier y ζ := by
    funext ζ
    change fourier (Matrix.circulant m *ᵥ y) ζ = fourier m ζ * fourier y ζ
    exact fourier_mulVec_circulant m y ζ
  have hpair := fourier_inner_eq_gridAvg y ((circulant m).mulVec y)
  rw [hdiag] at hpair
  unfold form pairing
  rw [hpair]
  exact re_gridAvg_star_mul_mul (fun ζ => fourier m ζ) (fun ζ => fourier y ζ)

lemma fourier_constInv (ζ : Torus d L) :
    fourier (fun _ : Torus d L => ((Fintype.card (Torus d L) : ℂ))⁻¹) ζ =
      if ζ = 0 then 1 else 0 := by
  have hcard : 0 < Fintype.card (Torus d L) := Fintype.card_pos_iff.mpr ⟨(0 : Torus d L)⟩
  have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hsum : ∑ x, star (character ζ x) =
      if ζ = 0 then (Fintype.card (Torus d L) : ℂ) else 0 := by
    have h := character_sum_orthog ζ 0
    simpa [character_zero_left] using h
  calc
    fourier (fun _ : Torus d L => ((Fintype.card (Torus d L) : ℂ))⁻¹) ζ =
        (Fintype.card (Torus d L) : ℂ)⁻¹ * ∑ x, star (character ζ x) := by
      unfold fourier
      rw [← Finset.mul_sum]
    _ = if ζ = 0 then 1 else 0 := by
      rw [hsum]
      by_cases hζ : ζ = 0 <;> simp [hζ, hN]

lemma meanProjection_eq_circulant_const (d L : ℕ) [NeZero L] :
    meanProjection (Torus d L) = circulant (fun _ => ((Fintype.card (Torus d L) : ℂ))⁻¹) := by
  ext x y
  simp [meanProjection, circulant]

def lapKernel : Torus d L → ℂ :=
  fun u => (2 * (d : ℂ)) * (deltaZero (d := d) (L := L) u) -
    ∑ j : Fin d,
      (deltaAt (d := d) (L := L) (basisStep (d := d) (L := L) j) u +
        deltaAt (d := d) (L := L) (-basisStep (d := d) (L := L) j) u)

lemma lapKernel_eq_sum_functions : lapKernel =
    (2 * (d : ℂ)) • deltaZero -
      ∑ j : Fin d,
        (deltaAt (d := d) (L := L) (basisStep (d := d) (L := L) j) +
          deltaAt (d := d) (L := L) (-basisStep (d := d) (L := L) j)) := by
  funext u
  simp [lapKernel, Pi.smul_apply]

lemma laplacian_eq_circulant_lapKernel (d L : ℕ) [NeZero L] :
    laplacian (d := d) (L := L) = circulant (lapKernel (d := d) (L := L)) := by
  ext x y
  have hplus : ∀ j : Fin d, (y = x + basisStep j) ↔ x - y = -basisStep j := by
    intro j
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      calc
        y = x - (x - y) := by abel
        _ = x - (-basisStep j) := by rw [h]
        _ = x + basisStep j := by abel
  have hminus : ∀ j : Fin d, (y = x - basisStep j) ↔ x - y = basisStep j := by
    intro j
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      calc
        y = x - (x - y) := by abel
        _ = x - basisStep j := by rw [h]
  simp [laplacian, lapKernel, freeHopping, circulant, Matrix.one_apply,
    hplus, hminus, deltaZero, deltaAt, sub_eq_zero]
  have hsum : ∑ j : Fin d,
        ((if x - y = -basisStep j then (1 : ℂ) else 0) +
          (if x - y = basisStep j then 1 else 0)) =
      ∑ j : Fin d,
        ((if x - y = basisStep j then (1 : ℂ) else 0) +
          (if x - y = -basisStep j then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

lemma fourier_lapKernel (ζ : Torus d L) :
    fourier lapKernel ζ = (laplacianSymbol (gridAngle ζ) : ℂ) := by
  rw [lapKernel_eq_sum_functions]
  rw [fourier_sub, fourier_smul, fourier_deltaZero, fourier_sum_functions]
  simp_rw [fourier_add, fourier_deltaAt]
  have htrig (j : Fin d) :
      star (character ζ (basisStep j)) + star (character ζ (-basisStep j)) =
        (2 * Real.cos (gridAngle ζ j) : ℂ) := by
    have hstep : character ζ (basisStep j) =
        Complex.exp (Complex.I * (gridAngle ζ j : ℂ)) := by
      rw [character_basisStep, gridAngle_apply, stdAddChar_eq_exp_angle]
    have hneg : character ζ (-basisStep j) =
        Complex.exp (-(Complex.I * (gridAngle ζ j : ℂ))) := by
      calc
        character ζ (-basisStep j) = (character ζ (basisStep j))⁻¹ :=
          AddChar.map_neg_eq_inv (characterAddChar ζ) (basisStep j)
        _ = Complex.exp (-(Complex.I * (gridAngle ζ j : ℂ))) := by
          rw [hstep, ← Complex.exp_neg]
    calc
      star (character ζ (basisStep j)) + star (character ζ (-basisStep j)) =
          character ζ (-basisStep j) + character ζ (basisStep j) := by
        rw [character_star, character_star]
        simp
      _ = Complex.exp (-(Complex.I * (gridAngle ζ j : ℂ))) +
          Complex.exp (Complex.I * (gridAngle ζ j : ℂ)) := by rw [hneg, hstep]
      _ = (2 * Real.cos (gridAngle ζ j) : ℂ) := by
        have hA : Complex.exp (Complex.I * (gridAngle ζ j : ℂ)) =
            (Real.cos (gridAngle ζ j) : ℂ) +
              (Real.sin (gridAngle ζ j) : ℂ) * Complex.I := by
          rw [show Complex.I * (gridAngle ζ j : ℂ) =
            (gridAngle ζ j : ℂ) * Complex.I by ring, Complex.exp_mul_I]
          simpa [Complex.ofReal_cos, Complex.ofReal_sin]
        have hB : Complex.exp (-(Complex.I * (gridAngle ζ j : ℂ))) =
            (Real.cos (gridAngle ζ j) : ℂ) -
              (Real.sin (gridAngle ζ j) : ℂ) * Complex.I := by
          rw [show -(Complex.I * (gridAngle ζ j : ℂ)) =
            (-(gridAngle ζ j) : ℝ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
          simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
            Complex.ofReal_sin]
          ring
        rw [hB, hA]
        ring
  simp_rw [htrig]
  calc
    (2 * (d : ℂ)) * 1 -
        ∑ j : Fin d, (2 * Real.cos (gridAngle ζ j) : ℂ) =
      ((2 * (d : ℝ) + dispersion (gridAngle ζ)) : ℂ) := by
        simp [dispersion]
        push_cast
        have hsum : ∑ j : Fin d, (2 : ℂ) * Complex.cos (gridAngle ζ j) =
            (∑ j : Fin d, Complex.cos (gridAngle ζ j)) * 2 := by
          calc
            ∑ j : Fin d, (2 : ℂ) * Complex.cos (gridAngle ζ j) =
                ∑ j : Fin d, Complex.cos (gridAngle ζ j) * 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ j : Fin d, Complex.cos (gridAngle ζ j)) * 2 :=
              (Finset.sum_mul ..).symm
        rw [hsum]
        ring
    _ = (laplacianSymbol (gridAngle ζ) : ℂ) := by
      rw [dispersion_identity_proof]
      push_cast
      ring

lemma fourier_zero_mode (y : Torus d L → ℂ) : fourier y 0 = ∑ x, y x := by
  unfold fourier
  simp [character_zero_left]

lemma circulant_add_local (m m' : Torus d L → ℂ) :
    circulant m + circulant m' = circulant (m + m') := by
  ext x y
  rfl

lemma circulant_smul_local (c : ℂ) (m : Torus d L → ℂ) :
    c • circulant m = circulant (c • m) := by
  ext x y
  rfl

lemma circulant_mul_local (m m' : Torus d L → ℂ) :
    ∃ m'' : Torus d L → ℂ, circulant m * circulant m' = circulant m'' ∧
      ∀ ζ, fourier m'' ζ = fourier m ζ * fourier m' ζ := by
  classical
  refine ⟨Matrix.circulant m *ᵥ m', ?_, ?_⟩
  · change Matrix.circulant m * Matrix.circulant m' =
      Matrix.circulant (Matrix.circulant m *ᵥ m')
    exact Matrix.circulant_mul m m'
  · intro ζ
    exact fourier_mulVec_circulant m m' ζ

theorem circulantCalculus_proof : CirculantCalculusStatement := by
  intro d L hNe hL
  constructor
  · intro m y
    exact circulant_form_diagonalized m y
  constructor
  · intro y
    exact fourier_parseval y
  constructor
  · intro y
    exact fourier_zero_mode y
  constructor
  · intro s
    exact ⟨inverseFourier s, fun ζ => fourier_inverseFourier s ζ⟩
  constructor
  · intro m m' h
    apply fourier_injective
    funext ζ
    exact h ζ
  constructor
  · intro m m'
    exact circulant_mul_local m m'
  constructor
  · intro m hm
    have hfour : fourier m = fourier deltaZero := by
      funext ζ
      rw [hm ζ, fourier_deltaZero]
    rw [fourier_injective hfour]
    exact circulant_deltaZero d L
  constructor
  · intro m m'
    exact ⟨circulant_add_local m m', fun ζ => fourier_add m m' ζ⟩
  constructor
  · intro c m
    exact ⟨circulant_smul_local c m, fun ζ => fourier_smul c m ζ⟩
  constructor
  · intro m hreal
    change (Matrix.circulant m).conjTranspose = Matrix.circulant m
    exact circulant_hermitian_of_real_symbol m hreal
  constructor
  · refine ⟨meanProjection_eq_circulant_const d L, ?_⟩
    intro ζ
    exact fourier_constInv ζ
  constructor
  · refine ⟨lapKernel, laplacian_eq_circulant_lapKernel d L, ?_⟩
    intro ζ
    exact fourier_lapKernel ζ
  · intro z hne ζ
    let s : Torus d L → ℂ := fun k => ((dispersion (gridAngle k) : ℂ) - z)⁻¹
    have hgreen : (fun x => freeGreen z x 0) = inverseFourier s := by
      funext x
      simp [freeGreen, inverseFourier, s, mul_comm]
    have hnorm : (fun x => ((‖freeGreen z x 0‖ ^ 2 : ℝ) : ℂ)) =
        (fun x => ((‖inverseFourier s x‖ ^ 2 : ℝ) : ℂ)) := by
      funext x
      rw [congrFun hgreen x]
    rw [hnorm]
    exact fourier_normSq_inverseFourier s ζ

end AndersonAC.S3
