import AndersonAC.S3.HelperStatements

noncomputable section
open scoped BigOperators
open AndersonAC.Blueprint
attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3

variable {d L : ℕ} [NeZero L]

/-- Centered integer lift of `ZMod L`: `val` if `2*val < L`, else `val - L`. -/
def centerInt (L : ℕ) (a : ZMod L) : ℤ :=
  if 2 * a.val < L then (a.val : ℤ) else (a.val : ℤ) - (L : ℤ)

lemma centerInt_cast (a : ZMod L) : ((centerInt L a : ℤ) : ZMod L) = a := by
  unfold centerInt
  split_ifs with h
  · simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · push_cast
    rw [ZMod.natCast_zmod_val a]
    simp

lemma centerReal_eq (a : ZMod L) :
    (if 2 * a.val < L then ((a.val : ℝ)) else ((a.val : ℝ)) - (L : ℝ))
      = ((centerInt L a : ℤ) : ℝ) := by
  unfold centerInt
  split_ifs with h
  · simp
  · push_cast
    ring

lemma gridAngle_eq_centerInt (k : Torus d L) (j : Fin d) :
    gridAngle k j = 2 * Real.pi * ((centerInt L (k j) : ℤ) : ℝ) / (L : ℝ) := by
  unfold gridAngle
  rw [centerReal_eq]

/-- Additivity of centered angles up to `2πℤ` (frozen P5). -/
lemma gridAngle_add_exists (k ζ : Torus d L) (j : Fin d) :
    ∃ n : ℤ, gridAngle (k + ζ) j
      = gridAngle k j + gridAngle ζ j + 2 * Real.pi * n := by
  have hj : (k + ζ) j = k j + ζ j := Pi.add_apply k ζ j
  rw [gridAngle_eq_centerInt, gridAngle_eq_centerInt, gridAngle_eq_centerInt, hj]
  have hcast : (((centerInt L (k j + ζ j) - centerInt L (k j)
      - centerInt L (ζ j) : ℤ)) : ZMod L) = 0 := by
    push_cast
    rw [centerInt_cast, centerInt_cast, centerInt_cast]
    simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  obtain ⟨n, hn⟩ := hcast
  refine ⟨n, ?_⟩
  have hD : centerInt L (k j + ζ j)
      = centerInt L (k j) + centerInt L (ζ j) + (L : ℤ) * n := by
    have : centerInt L (k j + ζ j) - centerInt L (k j) - centerInt L (ζ j)
        = (L : ℤ) * n := hn
    linarith
  have hL : (L : ℝ) ≠ 0 := by
    have : NeZero L := inferInstance
    have hL0 : 0 < L := NeZero.pos L
    positivity
  -- cast integer identity to reals and rearrange
  have hR : ((centerInt L (k j + ζ j) : ℤ) : ℝ)
      = ((centerInt L (k j) : ℤ) : ℝ) + ((centerInt L (ζ j) : ℤ) : ℝ)
        + (L : ℝ) * (n : ℝ) := by
    have := congrArg (fun z : ℤ => ((z : ℝ))) hD
    simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast] using this
  rw [hR]
  field_simp

/-- Negation of centered angles up to `2πℤ` (frozen P6). -/
lemma gridAngle_neg_exists (k : Torus d L) (j : Fin d) :
    ∃ n : ℤ, gridAngle (-k) j = -gridAngle k j + 2 * Real.pi * n := by
  have hj : (-k) j = -(k j) := Pi.neg_apply k j
  rw [gridAngle_eq_centerInt, gridAngle_eq_centerInt, hj]
  have hcast : (((centerInt L (-(k j)) + centerInt L (k j) : ℤ)) : ZMod L) = 0 := by
    push_cast
    rw [centerInt_cast, centerInt_cast]
    simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  obtain ⟨n, hn⟩ := hcast
  refine ⟨n, ?_⟩
  have hD : centerInt L (-(k j))
      = -(centerInt L (k j)) + (L : ℤ) * n := by
    have : centerInt L (-(k j)) + centerInt L (k j) = (L : ℤ) * n := hn
    linarith
  have hL : (L : ℝ) ≠ 0 := by
    have hL0 : 0 < L := NeZero.pos L
    positivity
  have hR : ((centerInt L (-(k j)) : ℤ) : ℝ)
      = -((centerInt L (k j) : ℤ) : ℝ) + (L : ℝ) * (n : ℝ) := by
    have := congrArg (fun z : ℤ => ((z : ℝ))) hD
    simpa [Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using this
  rw [hR]
  field_simp

/-! ### One-dimensional geometric orthogonality -/

/-- Primitive root `exp(2πI d/L)` has `L`-th power `1`. -/
lemma primRoot_pow (dd : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ))) ^ L = 1 := by
  have hL : (L : ℂ) ≠ 0 := by
    have hL0 : 0 < L := NeZero.pos L
    exact_mod_cast ne_of_gt hL0
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ)) ^ L
      = Complex.exp (((L : ℕ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ))) :=
    (Complex.exp_nat_mul _ L).symm
  rw [h2]
  have h3 : (((L : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ)))
      = (dd : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  rw [h3]
  exact Complex.exp_int_mul_two_pi_mul_I dd

/-- `exp(2πI d/L) = 1` iff `L ∣ d`. -/
lemma primRoot_eq_one_iff (dd : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ)) = 1
      ↔ (L : ℤ) ∣ dd := by
  have hL : (L : ℂ) ≠ 0 := by
    have hL0 : 0 < L := NeZero.pos L
    exact_mod_cast ne_of_gt hL0
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    -- hn : 2*π*I*d/L = n*(2*π*I); cancel 2*π*I
    have hmul : (2 * (Real.pi : ℂ) * Complex.I) * ((dd : ℂ) / (L : ℂ))
        = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      have h1 : 2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ)
          = (2 * (Real.pi : ℂ) * Complex.I) * ((dd : ℂ) / (L : ℂ)) := by
        ring
      rw [h1] at hn
      have h2 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by ring
      rw [h2] at hn
      exact hn
    have hdiv : (dd : ℂ) / (L : ℂ) = (n : ℂ) :=
      mul_left_cancel₀ hpi hmul
    have hdvdC : (dd : ℂ) = (((L : ℤ) * n : ℤ) : ℂ) := by
      have hLn : (((L : ℤ) : ℂ)) = (L : ℂ) := by
        simp [Int.cast_natCast]
      rw [Int.cast_mul, hLn]
      have hdeq : (dd : ℂ) = (L : ℂ) * (n : ℂ) := by
        have := (div_eq_iff hL).mp hdiv
        -- this : dd = n * L; rearrange
        rw [this]; ring
      rw [hdeq]
    have hdvd : dd = (L : ℤ) * n := Int.cast_injective hdvdC
    exact ⟨n, hdvd⟩
  · intro h
    obtain ⟨n, hn⟩ := h
    have : 2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / (L : ℂ)
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hn]
      push_cast
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I n

/-- One-dimensional orthogonality: sum of roots over `ZMod L`. -/
lemma oneDimSum (dd : ℤ) :
    (∑ t : ZMod L,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) * ((t.val : ℕ) : ℂ)
        / (L : ℂ)))
      = if (L : ℤ) ∣ dd then (L : ℂ) else 0 := by
  have hLpos : 0 < L := NeZero.pos L
  have hLne : L ≠ 0 := ne_of_gt hLpos
  obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := Nat.exists_eq_succ_of_ne_zero hLne
  subst hm
  -- primitive root
  set r : ℂ := Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / ((m + 1 : ℕ) : ℂ)) with hr
  have hrL : r ^ (m + 1) = 1 := primRoot_pow dd
  have hexp : ∀ t : ZMod (m + 1),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) * ((t.val : ℕ) : ℂ)
        / ((m + 1 : ℕ) : ℂ)) = r ^ t.val := by
    intro t
    rw [hr]
    have : 2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) * ((t.val : ℕ) : ℂ)
          / ((m + 1 : ℕ) : ℂ)
        = ((t.val : ℕ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I * (dd : ℂ) / ((m + 1 : ℕ) : ℂ)) := by
      ring
    rw [this, ← Complex.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun t _ => hexp t)]
  -- convert sum over ZMod (Fin) to range
  have hsum : (∑ t : ZMod (m + 1), r ^ t.val)
      = ∑ i ∈ Finset.range (m + 1), r ^ i := by
    have : (∑ t : ZMod (m + 1), r ^ t.val)
        = ∑ i : Fin (m + 1), r ^ (i.val : ℕ) := rfl
    rw [this]
    exact Fin.sum_univ_eq_sum_range (fun n => r ^ n) (m + 1)
  rw [hsum]
  by_cases hdiv : (((m + 1 : ℕ) : ℤ)) ∣ dd
  · simp only [hdiv, ite_true]
    have hr1 : r = 1 := (primRoot_eq_one_iff dd).mpr hdiv
    rw [hr1]
    simp
  · simp only [hdiv, ite_false]
    have hr1 : r ≠ 1 := fun heq => hdiv ((primRoot_eq_one_iff dd).mp heq)
    rw [geom_sum_eq hr1]
    rw [hrL]
    simp

/-! ### Character sums as products -/

open ComplexConjugate in
lemma character_star_eq (k x : Torus d L) :
    star (character k x)
      = Complex.exp (-Complex.I * ((∑ j, gridAngle k j * ((x j).val : ℝ)) : ℝ)) := by
  unfold character
  show (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul]
  rw [Complex.conj_I, Complex.conj_ofReal]

lemma character_norm_eq (k x : Torus d L) : ‖character k x‖ = 1 := by
  unfold character
  exact Complex.norm_exp_I_mul_ofReal _

/-- Grid angle as complex number via centered lift. -/
lemma gridAngle_C (k : Torus d L) (j : Fin d) :
    ((gridAngle k j : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) * ((centerInt L (k j) : ℤ) : ℂ) / (L : ℂ) := by
  rw [gridAngle_eq_centerInt]
  push_cast
  ring

/-- Character in sum-of-casts form over `ℂ`. -/
lemma character_C_eq (k x : Torus d L) :
    character k x = Complex.exp (Complex.I *
      ∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ)) := by
  unfold character
  congr 1
  congr 1
  push_cast
  ring

open ComplexConjugate in
lemma character_star_C_eq (k x : Torus d L) :
    star (character k x) = Complex.exp (-Complex.I *
      ∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ)) := by
  rw [character_star_eq]
  congr 1
  congr 1
  push_cast
  ring

/-- Product form of `character k x * star (character k' x)`. -/
lemma charMulStar_eq_prod (k k' x : Torus d L) :
    character k x * star (character k' x)
      = ∏ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((centerInt L (k j) - centerInt L (k' j) : ℤ)) : ℂ)
        * (((x j).val : ℕ) : ℂ) / (L : ℂ)) := by
  rw [character_C_eq, character_star_C_eq, ← Complex.exp_add,
    ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  ext j
  rw [gridAngle_C, gridAngle_C]
  push_cast
  ring

/-- Row orthogonality of characters. -/
lemma orthRow (k k' : Torus d L) :
    (∑ x : Torus d L, character k x * star (character k' x))
      = if k = k' then ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0 := by
  have hprod : ∀ x : Torus d L,
      character k x * star (character k' x)
        = ∏ j, (fun (jj : Fin d) (t : ZMod L) =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I
            * (((centerInt L (k jj) - centerInt L (k' jj) : ℤ)) : ℂ)
            * (((t.val : ℕ)) : ℂ) / (L : ℂ))) j (x j) := by
    intro x
    rw [charMulStar_eq_prod]
  rw [Finset.sum_congr rfl (fun x _ => hprod x)]
  have hfact : (∑ x : Torus d L, ∏ j, (fun (jj : Fin d) (t : ZMod L) =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * (((centerInt L (k jj) - centerInt L (k' jj) : ℤ)) : ℂ)
          * (((t.val : ℕ)) : ℂ) / (L : ℂ))) j (x j))
      = ∏ j, ∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((centerInt L (k j) - centerInt L (k' j) : ℤ)) : ℂ)
        * (((t.val : ℕ)) : ℂ) / (L : ℂ)) := by
    have hps := Fintype.prod_sum (fun (jj : Fin d) (t : ZMod L) =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((centerInt L (k jj) - centerInt L (k' jj) : ℤ)) : ℂ)
        * (((t.val : ℕ)) : ℂ) / (L : ℂ)))
    rw [hps]
  rw [hfact]
  have h1d : ∀ j : Fin d,
      (∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((centerInt L (k j) - centerInt L (k' j) : ℤ)) : ℂ)
        * (((t.val : ℕ)) : ℂ) / (L : ℂ)))
      = if (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j)) then (L : ℂ) else 0 :=
    fun j => oneDimSum (centerInt L (k j) - centerInt L (k' j))
  have hprod_if : (∏ j, ∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((centerInt L (k j) - centerInt L (k' j) : ℤ)) : ℂ)
        * (((t.val : ℕ)) : ℂ) / (L : ℂ)))
      = ∏ j, (if (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j))
        then (L : ℂ) else 0) :=
    Finset.prod_congr rfl (fun j _ => h1d j)
  rw [hprod_if]
  -- It remains to show product of ifs equals N·[k=k'].
  -- First: (∀ j, L ∣ diff j) ↔ k = k'.
  have hiff : (∀ j, (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j))) ↔ k = k' := by
    constructor
    · intro hall
      funext j
      -- from L ∣ (c - c') deduce val equality
      have hdiv := hall j
      have hcc : ((centerInt L (k j) - centerInt L (k' j) : ℤ) : ZMod L) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hdiv
      push_cast at hcc
      rw [centerInt_cast, centerInt_cast] at hcc
      -- hcc : k j - k' j = 0 in ZMod L
      have heq : k j - k' j = 0 := hcc
      have : k j = k' j := sub_eq_zero.mp heq
      exact this
    · intro heq j
      rw [heq]
      simp
  -- card Torus = L ^ d
  have hcard : Fintype.card (Torus d L) = L ^ d := by
    have h1 : Fintype.card (Torus d L) = ∏ _j : Fin d, Fintype.card (ZMod L) :=
      Fintype.card_pi
    rw [h1]
    simp [ZMod.card]
  by_cases hk : k = k'
  · rw [if_pos hk]
    have hall : ∀ j, (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j)) := by
      intro j; rw [hk]; simp
    have hprod_eq : (∏ j, (if (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j))
        then (L : ℂ) else 0)) = ∏ _j : Fin d, (L : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [if_pos (hall j)]
    rw [hprod_eq]
    have hLpow : (∏ _j : Fin d, (L : ℂ)) = (((L ^ d : ℕ)) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hLpow, hcard]
  · simp only [hk, ite_false]
    have hnotall : ¬ ∀ j, (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j)) := by
      intro hall
      apply hk
      exact hiff.mp hall
    push Not at hnotall
    obtain ⟨j0, hj0⟩ := hnotall
    have hzero : (∏ j, (if (L : ℤ) ∣ (centerInt L (k j) - centerInt L (k' j))
        then (L : ℂ) else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j0)
      rw [if_neg hj0]
    exact hzero

/-- Centered vs val exponentials agree up to `2πℤ`. -/
lemma expCenter_eq_expVal (t : ZMod L) (mm : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((centerInt L t : ℤ) : ℂ)
      * (mm : ℂ) / (L : ℂ))
    = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((t.val : ℕ)) : ℂ)
      * (mm : ℂ) / (L : ℂ)) := by
  have hdelta : ∃ δ : ℤ, centerInt L t = (t.val : ℤ) - (L : ℤ) * δ := by
    unfold centerInt
    split_ifs with h
    · exact ⟨0, by simp⟩
    · exact ⟨1, by ring⟩
  obtain ⟨δ, hδ⟩ := hdelta
  have hL : (L : ℂ) ≠ 0 := by
    have hL0 : 0 < L := NeZero.pos L
    exact_mod_cast ne_of_gt hL0
  have hexp_diff : (2 * (Real.pi : ℂ) * Complex.I * ((centerInt L t : ℤ) : ℂ)
      * (mm : ℂ) / (L : ℂ))
      - (2 * (Real.pi : ℂ) * Complex.I * (((t.val : ℕ)) : ℂ)
        * (mm : ℂ) / (L : ℂ))
      = (-(δ * mm) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hδ]
    push_cast
    field_simp
    ring
  have hcorr : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I
      * ((centerInt L t : ℤ) : ℂ) * (mm : ℂ) / (L : ℂ))
      - (2 * (Real.pi : ℂ) * Complex.I * (((t.val : ℕ)) : ℂ)
        * (mm : ℂ) / (L : ℂ))) = 1 := by
    rw [hexp_diff]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hadd : Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((centerInt L t : ℤ) : ℂ) * (mm : ℂ) / (L : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((t.val : ℕ)) : ℂ)
        * (mm : ℂ) / (L : ℂ)
        + ((2 * (Real.pi : ℂ) * Complex.I * ((centerInt L t : ℤ) : ℂ)
          * (mm : ℂ) / (L : ℂ))
          - (2 * (Real.pi : ℂ) * Complex.I * (((t.val : ℕ)) : ℂ)
            * (mm : ℂ) / (L : ℂ)))) := by
    congr 1
    ring
  rw [hadd, Complex.exp_add, hcorr, mul_one]

/-- Dual product form: `star (character k x) * character k y` as product. -/
lemma charDual_eq_prod (k : Torus d L) (x y : Torus d L) :
    star (character k x) * character k y
      = ∏ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((centerInt L (k j) : ℤ) : ℂ)
        * (((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) : ℤ) : ℂ) / (L : ℂ)) := by
  rw [character_C_eq k y, character_star_C_eq k x, ← Complex.exp_add,
    ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  ext j
  rw [gridAngle_C]
  push_cast
  ring

/-- Column (dual) orthogonality with star. -/
lemma orthCol (x y : Torus d L) :
    (∑ k : Torus d L, star (character k x) * character k y)
      = if x = y then ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0 := by
  have hprod : ∀ k : Torus d L,
      star (character k x) * character k y
        = ∏ j, (fun (jj : Fin d) (t : ZMod L) =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t.val : ℕ) : ℂ)
            * (((((y jj).val : ℕ) : ℤ) - ((x jj).val : ℤ) : ℤ) : ℂ) / (L : ℂ)))
          j (k j) := by
    intro k
    rw [charDual_eq_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact expCenter_eq_expVal (k j) (((y j).val : ℤ) - ((x j).val : ℤ))
  rw [Finset.sum_congr rfl (fun k _ => hprod k)]
  have hfact : (∑ k : Torus d L, ∏ j, (fun (jj : Fin d) (t : ZMod L) =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t.val : ℕ) : ℂ)
          * (((((y jj).val : ℕ) : ℤ) - ((x jj).val : ℤ) : ℤ) : ℂ) / (L : ℂ))) j (k j))
      = ∏ j, ∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((t.val : ℕ) : ℂ)
        * (((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) : ℤ) : ℂ) / (L : ℂ)) := by
    have hps := Fintype.prod_sum (fun (jj : Fin d) (t : ZMod L) =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t.val : ℕ) : ℂ)
        * (((((y jj).val : ℕ) : ℤ) - ((x jj).val : ℤ) : ℤ) : ℂ) / (L : ℂ)))
    rw [hps]
  rw [hfact]
  -- 1D sums: ∑_t exp(2πI val(t) m /L) = L·[L∣m] where m = val(y)-val(x)
  have h1d : ∀ j : Fin d,
      (∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((t.val : ℕ) : ℂ)
        * (((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) : ℤ) : ℂ) / (L : ℂ)))
      = if (L : ℤ) ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ))
        then (L : ℂ) else 0 := by
    intro j
    -- rewrite exponent to oneDimSum form: 2*π*I*m*val/L vs 2*π*I*m*val/L (comm val*m)
    have hexp : ∀ t : ZMod L,
        (2 * (Real.pi : ℂ) * Complex.I * ((t.val : ℕ) : ℂ)
          * (((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) : ℤ) : ℂ) / (L : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I * (((((y j).val : ℕ) : ℤ)
          - ((x j).val : ℤ) : ℤ) : ℂ) * (((t.val : ℕ)) : ℂ) / (L : ℂ) := by
      intro t; ring
    simp_rw [hexp]
    exact oneDimSum _
  have hprod_if : (∏ j, ∑ t : ZMod L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((t.val : ℕ) : ℂ)
        * (((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) : ℤ) : ℂ) / (L : ℂ)))
      = ∏ j, (if (L : ℤ) ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ))
        then (L : ℂ) else 0) :=
    Finset.prod_congr rfl (fun j _ => h1d j)
  rw [hprod_if]
  have hiff : (∀ j, (L : ℤ) ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)))
      ↔ x = y := by
    constructor
    · intro hall
      funext j
      have hdiv := hall j
      -- |val(y)-val(x)| < L, so divisibility forces equality
      have hval_lt : ∀ a : ZMod L, a.val < L := fun a => a.val_lt
      have h1 := hval_lt (y j)
      have h2 := hval_lt (x j)
      have hint : (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) = 0 := by
        -- use Int interval: -(L-1) ≤ diff ≤ L-1, divisible by L → 0
        have hbound : -(L : ℤ) < (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)
            ∧ (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) < (L : ℤ) := by
          have hy0 : 0 ≤ (((y j).val : ℕ) : ℤ) := Int.ofNat_nonneg _
          have hx0 : 0 ≤ (((x j).val : ℕ) : ℤ) := Int.ofNat_nonneg _
          have hyL : (((y j).val : ℕ) : ℤ) < (L : ℤ) := by
            exact_mod_cast h1
          have hxL : (((x j).val : ℕ) : ℤ) < (L : ℤ) := by
            exact_mod_cast h2
          have hLpos : 0 < (L : ℤ) := by
            have : 0 < L := NeZero.pos L
            exact_mod_cast this
          constructor <;> omega
        -- divisibility + bounds → 0
        obtain ⟨cc, hcc⟩ := hdiv
        -- diff = L*cc, |diff|<L → cc=0
        have hcc0 : cc = 0 := by
          have hLpos : 0 < (L : ℤ) := by
            have : 0 < L := NeZero.pos L
            exact_mod_cast this
          by_contra hne
          have habs : (L : ℤ) ≤ (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)
              ∨ (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) ≤ -(L : ℤ) := by
            have : (((y j).val : ℕ) : ℤ) - ((x j).val : ℤ) = (L : ℤ) * cc := hcc
            rw [this]
            by_cases hccpos : 0 < cc
            · left
              have : (L : ℤ) * 1 ≤ (L : ℤ) * cc := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hLpos)
                omega
              simpa using this
            · right
              push_neg at hccpos
              have hccneg : cc ≤ -1 := by omega
              have : (L : ℤ) * cc ≤ (L : ℤ) * (-1) := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hLpos)
                exact hccneg
              simpa using this
          omega
        rw [hcc0, mul_zero] at hcc
        exact hcc
      -- val equality → ZMod equality
      have hval_eq : (y j).val = (x j).val := by
        have := congrArg (fun z : ℤ => z) hint
        simp at this ⊢
        omega
      exact (ZMod.val_injective L hval_eq).symm
    · intro heq j
      rw [heq]
      simp
  have hcard : Fintype.card (Torus d L) = L ^ d := by
    have h1 : Fintype.card (Torus d L) = ∏ _j : Fin d, Fintype.card (ZMod L) :=
      Fintype.card_pi
    rw [h1]
    simp [ZMod.card]
  by_cases hk : x = y
  · rw [if_pos hk]
    have hall : ∀ j, (L : ℤ) ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)) := by
      intro j; rw [hk]; simp
    have hprod_eq : (∏ j, (if (L : ℤ)
        ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)) then (L : ℂ) else 0))
        = ∏ _j : Fin d, (L : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [if_pos (hall j)]
    rw [hprod_eq]
    have hLpow : (∏ _j : Fin d, (L : ℂ)) = (((L ^ d : ℕ)) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hLpow, hcard]
  · rw [if_neg hk]
    have hnotall : ¬ ∀ j, (L : ℤ)
        ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)) := by
      intro hall
      apply hk
      exact hiff.mp hall
    push Not at hnotall
    obtain ⟨j0, hj0⟩ := hnotall
    have hzero : (∏ j, (if (L : ℤ)
        ∣ ((((y j).val : ℕ) : ℤ) - ((x j).val : ℤ)) then (L : ℂ) else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j0)
      rw [if_neg hj0]
    exact hzero

/-- General Parseval: `normSq` equals averaged squared Fourier magnitudes. -/
lemma parseval (v : Torus d L → ℂ) :
    normSq v = gridAvgReal (fun k => ‖fourier v k‖ ^ 2) := by
  apply Complex.ofReal_injective
  have hNpos : 0 < Fintype.card (Torus d L) := Fintype.card_pos
  have hNR : ((Fintype.card (Torus d L) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hNpos
  have hNC : ((Fintype.card (Torus d L) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hNpos
  have hnorm : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * star z := by
    intro z
    have h1 : (((‖z‖ ^ 2 : ℝ)) : ℂ) = (((Complex.normSq z : ℝ)) : ℂ) := by
      rw [Complex.normSq_eq_norm_sq]
    rw [h1]
    exact (Complex.mul_conj z).symm
  unfold normSq gridAvgReal fourier
  rw [Complex.ofReal_sum]
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [hnorm]
  -- Expand Fourier products into double sums.
  have hstar_four : ∀ k : Torus d L,
      star (∑ x : Torus d L, v x * star (character k x))
        = ∑ y : Torus d L, star (v y) * character k y := by
    intro k
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [star_mul, star_star]
    ring
  simp_rw [hstar_four]
  have hexpand : ∀ k : Torus d L,
      (∑ x : Torus d L, v x * star (character k x))
        * (∑ y : Torus d L, star (v y) * character k y)
      = ∑ x : Torus d L, ∑ y : Torus d L,
        v x * star (v y) * (star (character k x) * character k y) := by
    intro k
    rw [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hexpand]
  -- Swap sums: Σ_k Σ_x Σ_y = Σ_x Σ_y Σ_k.
  have hswap : (∑ k : Torus d L, ∑ x : Torus d L, ∑ y : Torus d L,
        v x * star (v y) * (star (character k x) * character k y))
      = ∑ x : Torus d L, ∑ y : Torus d L,
        v x * star (v y) * (∑ k : Torus d L,
          star (character k x) * character k y) := by
    have h1 : (∑ k : Torus d L, ∑ x : Torus d L, ∑ y : Torus d L,
          v x * star (v y) * (star (character k x) * character k y))
        = ∑ x : Torus d L, ∑ k : Torus d L, ∑ y : Torus d L,
          v x * star (v y) * (star (character k x) * character k y) := by
      apply Finset.sum_comm
    rw [h1]
    apply Finset.sum_congr rfl
    intro x _
    have h2 : (∑ k : Torus d L, ∑ y : Torus d L,
          v x * star (v y) * (star (character k x) * character k y))
        = ∑ y : Torus d L, ∑ k : Torus d L,
          v x * star (v y) * (star (character k x) * character k y) := by
      apply Finset.sum_comm
    rw [h2]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum]
  rw [hswap]
  -- Apply column orthogonality.
  simp_rw [orthCol]
  -- Now Σ_x Σ_y v x star(v y) * (if x=y then N else 0) = N * Σ_x v x star(v x).
  have hdiag : (∑ x : Torus d L, ∑ y : Torus d L,
        v x * star (v y) * (if x = y then ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0))
      = ((Fintype.card (Torus d L) : ℕ) : ℂ) * ∑ x : Torus d L, v x * star (v x) := by
    have hinner : ∀ x : Torus d L,
        (∑ y : Torus d L, v x * star (v y)
          * (if x = y then ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0))
        = v x * star (v x) * ((Fintype.card (Torus d L) : ℕ) : ℂ) := by
      intro x
      have hite : ∀ y : Torus d L,
          v x * star (v y) * (if x = y then ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0)
          = if x = y then v x * star (v y) * ((Fintype.card (Torus d L) : ℕ) : ℂ) else 0 := by
        intro y
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy]
      simp_rw [hite]
      rw [Finset.sum_ite_eq]
      simp
    simp_rw [hinner]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hdiag]
  push_cast
  field_simp

/-- Character is additive in `x`. -/
lemma charAddX (k x y : Torus d L) :
    character k (x + y) = character k x * character k y := by
  have hLpos : 0 < L := NeZero.pos L
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hLpos
  have hval_add : ∀ j : Fin d, ((x + y) j).val = ((x j).val + (y j).val) % L := by
    intro j
    have hj : (x + y) j = x j + y j := Pi.add_apply x y j
    rw [hj]
    exact ZMod.val_add _ _
  set t : Fin d → ℕ := fun j => ((x j).val + (y j).val) / L with ht
  have hcarry : ∀ j, (((x + y) j).val : ℤ) + (L : ℤ) * ((t j : ℕ) : ℤ)
      = ((x j).val : ℤ) + ((y j).val : ℤ) := by
    intro j
    have h1 : ((x j).val + (y j).val) % L + L * (((x j).val + (y j).val) / L)
        = (x j).val + (y j).val := Nat.mod_add_div _ _
    have h2 : ((x + y) j).val = ((x j).val + (y j).val) % L := hval_add j
    have htj : t j = ((x j).val + (y j).val) / L := rfl
    have h1Z := congrArg (fun n : ℕ => (n : ℤ)) h1
    rw [← h2] at h1Z
    push_cast at h1Z
    -- h1Z : ((x+y).val:ℤ) + L*(.../L:ℤ) = ...
    have htjZ : ((t j : ℕ) : ℤ) = ((((x j).val + (y j).val) / L : ℕ) : ℤ) := by
      rw [htj]
    rw [htjZ]
    exact h1Z
  set M : ℤ := ∑ j, centerInt L (k j) * ((t j : ℕ) : ℤ) with hM
  have hexp_eq : Complex.I * (∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((x + y) j).val : ℕ) : ℂ))
      = Complex.I * (∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ))
        + Complex.I * (∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((y j).val : ℕ)) : ℂ))
        + ((-(M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    simp_rw [Finset.mul_sum]
    have hM_C : ((-(M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = ∑ j, ((-(centerInt L (k j) * ((t j : ℕ) : ℤ) : ℤ) : ℂ)
          * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [hM]
      push_cast
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    rw [hM_C]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    -- per-coordinate: I*θ*val(x+y) = I*θ*val(x) + I*θ*val(y) + (-c*t)*2πI
    -- Use htheta (θ*L=2πc) and hcarryC (val+L*t=...) via linear combination, no division.
    have htheta : ((gridAngle k j : ℝ) : ℂ) * (L : ℂ)
        = 2 * (Real.pi : ℂ) * ((centerInt L (k j) : ℤ) : ℂ) := by
      rw [gridAngle_C]
      field_simp
    have hcarryC : ((((x + y) j).val : ℕ) : ℂ) + (L : ℂ) * ((((t j : ℕ))) : ℂ)
        = ((((x j).val : ℕ)) : ℂ) + ((((y j).val : ℕ)) : ℂ) := by
      have hcj := hcarry j
      have := congrArg (fun z : ℤ => (z : ℂ)) hcj
      simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast] using this
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    linear_combination (Complex.I * ((gridAngle k j : ℝ) : ℂ)) * hcarryC
      + (-Complex.I * ((((t j : ℕ))) : ℂ)) * htheta
  rw [character_C_eq, character_C_eq, character_C_eq, hexp_eq, Complex.exp_add,
    Complex.exp_add]
  have hcorr : Complex.exp (((-(M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    have : ((-(M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = ((-(M) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hcorr, mul_one]

/-- Character of negation equals star. -/
lemma charNegX (k x : Torus d L) :
    character k (-x) = star (character k x) := by
  have hLpos : 0 < L := NeZero.pos L
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hLpos
  -- δ_j = 0 if x j = 0 else 1, with val(-x)+val(x) = L*δ.
  classical
  set δ : Fin d → ℕ := fun j => if x j = 0 then 0 else 1 with hδ
  have hcarryNeg : ∀ j, (((-x) j).val : ℤ) + ((x j).val : ℤ)
      = (L : ℤ) * ((δ j : ℕ) : ℤ) := by
    intro j
    have hj : (-x) j = -(x j) := Pi.neg_apply x j
    by_cases hx : x j = 0
    · have hneg : (-x) j = 0 := by rw [hj, hx, neg_zero]
      have hval_neg : ((-x) j).val = 0 := by rw [hneg, ZMod.val_zero]
      have hval_x : (x j).val = 0 := by rw [hx, ZMod.val_zero]
      have hδ0 : δ j = 0 := by simp [hδ, hx]
      rw [hval_neg, hval_x, hδ0]
      simp
    · have hne : NeZero (x j) := ⟨hx⟩
      have hval_neg : ((-x) j).val = L - (x j).val := by
        rw [hj]
        exact ZMod.val_neg_of_ne_zero (x j)
      have hδ1 : δ j = 1 := by simp [hδ, hx]
      have hlt : (x j).val < L := (x j).val_lt
      have hle : (x j).val ≤ L := Nat.le_of_lt hlt
      have hval_eq : L - (x j).val + (x j).val = L := Nat.sub_add_cancel hle
      have hgoal : (((-x) j).val : ℤ) + ((x j).val : ℤ) = (L : ℤ) * 1 := by
        rw [hval_neg]
        -- (L - val : ℕ):ℤ + (val:ℕ):ℤ = (L:ℤ)
        omega
      simpa [hδ1] using hgoal
  set M : ℤ := ∑ j, centerInt L (k j) * ((δ j : ℕ) : ℤ) with hM
  rw [character_C_eq, character_star_C_eq]
  have hexp_eq : Complex.I * (∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((-x) j).val : ℕ) : ℂ))
      = -Complex.I * (∑ j, ((gridAngle k j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ))
        + ((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp_rw [Finset.mul_sum]
    have hM_C : (((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = ∑ j, (((centerInt L (k j) * ((δ j : ℕ) : ℤ) : ℤ) : ℂ)
          * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [hM]
      push_cast
      rw [Finset.sum_mul]
    rw [hM_C]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have htheta : ((gridAngle k j : ℝ) : ℂ) * (L : ℂ)
        = 2 * (Real.pi : ℂ) * ((centerInt L (k j) : ℤ) : ℂ) := by
      rw [gridAngle_C]
      field_simp
    have hcarryC : ((((-x) j).val : ℕ) : ℂ) + ((((x j).val : ℕ)) : ℂ)
        = (L : ℂ) * ((((δ j : ℕ))) : ℂ) := by
      have hcj := hcarryNeg j
      have := congrArg (fun z : ℤ => (z : ℂ)) hcj
      simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast] using this
    simp only [Int.cast_mul, Int.cast_natCast]
    linear_combination (Complex.I * ((gridAngle k j : ℝ) : ℂ)) * hcarryC
      + (Complex.I * ((((δ j : ℕ))) : ℂ)) * htheta
  have hcorr : Complex.exp (((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I M
  rw [hexp_eq, Complex.exp_add, hcorr, mul_one]

/-- Character of subtraction. -/
lemma charSubX (k x y : Torus d L) :
    character k (x - y) = character k x * star (character k y) := by
  rw [sub_eq_add_neg, charAddX, charNegX]

/-- Character is additive in `k`. -/
lemma charAddK (k1 k2 x : Torus d L) :
    character (k1 + k2) x = character k1 x * character k2 x := by
  choose nn hnn using fun j => gridAngle_add_exists k1 k2 j
  -- nn j : ℤ with gridAngle(k1+k2) j = ... + 2π nn j
  set M : ℤ := ∑ j, nn j * (((x j).val : ℕ) : ℤ) with hM
  rw [character_C_eq, character_C_eq, character_C_eq]
  have hexp_eq : Complex.I * (∑ j, ((gridAngle (k1 + k2) j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ))
      = Complex.I * (∑ j, ((gridAngle k1 j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ))
        + Complex.I * (∑ j, ((gridAngle k2 j : ℝ) : ℂ) * ((((x j).val : ℕ)) : ℂ))
        + ((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hgrid : ∀ j : Fin d, ((gridAngle (k1 + k2) j : ℝ) : ℂ)
        = ((gridAngle k1 j : ℝ) : ℂ) + ((gridAngle k2 j : ℝ) : ℂ)
          + 2 * (Real.pi : ℂ) * ((nn j : ℤ) : ℂ) := by
      intro j
      have hj := hnn j
      have hjC : ((gridAngle (k1 + k2) j : ℝ) : ℂ)
          = ((gridAngle k1 j + gridAngle k2 j + 2 * Real.pi * (nn j : ℤ) : ℝ) : ℂ) := by
        rw [hj]
      rw [hjC]
      push_cast
      ring
    simp_rw [hgrid]
    simp_rw [Finset.mul_sum, add_mul]
    have hM_C : (((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = ∑ j, (((nn j * (((x j).val : ℕ) : ℤ) : ℤ) : ℂ)
          * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [hM]
      push_cast
      rw [Finset.sum_mul]
    rw [hM_C]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hexp_eq, Complex.exp_add, Complex.exp_add]
  have hcorr : Complex.exp (((M : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I M
  rw [hcorr, mul_one]

/-- Character at zero is one. -/
lemma char_zero (k : Torus d L) : character k 0 = 1 := by
  unfold character
  have h0 : (∑ j, gridAngle k j * (((0 : Torus d L) j).val : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj0 : ((0 : Torus d L) j).val = 0 := by
      have : (0 : Torus d L) j = 0 := Pi.zero_apply j
      rw [this, ZMod.val_zero]
    simp [hj0]
  rw [h0]
  simp

/-- Character of zero frequency is one. -/
lemma char_zero_freq (x : Torus d L) : character 0 x = 1 := by
  have hθ : ∀ j : Fin d, gridAngle (0 : Torus d L) j = 0 := by
    intro j
    unfold gridAngle
    have hval : ((0 : Torus d L) j).val = 0 := by
      have : (0 : Torus d L) j = 0 := Pi.zero_apply j
      rw [this, ZMod.val_zero]
    rw [hval]
    simp
  unfold character
  have h0 : (∑ j, gridAngle (0 : Torus d L) j * ((x j).val : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hθ j, zero_mul]
  rw [h0]
  simp

/-- Character at basis step is single exponential. -/
lemma charBasis (k : Torus d L) (j : Fin d) (hL : 1 < L) :
    character k (basisStep j) = Complex.exp (Complex.I * ((gridAngle k j : ℝ) : ℂ)) := by
  have hLne1 : L ≠ 1 := by omega
  rw [character_C_eq]
  congr 1
  congr 1
  have hval : ∀ j' : Fin d, ((((basisStep (d:=d) (L:=L) j j') : ZMod L).val : ℕ) : ℂ)
      = if j' = j then 1 else 0 := by
    intro j'
    have hsingle : (basisStep (d:=d) (L:=L) j j') = (if j' = j then 1 else 0 : ZMod L) := by
      unfold basisStep
      rw [Pi.single_apply]
    rw [hsingle]
    by_cases hjj : j' = j
    · simp [hjj, ZMod.val_one'' hLne1]
    · simp [hjj]
  simp_rw [hval]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Free hopping eigenvalue on characters. -/
lemma hoppingEigen (k : Torus d L) (x : Torus d L) (hL : 4 ≤ L) :
    (freeHopping.mulVec fun y => character k y) x
      = ((dispersion (gridAngle k) : ℝ) : ℂ) * character k x := by
  have h1L : 1 < L := by omega
  have hcos (j : Fin d) : character k (basisStep j) + star (character k (basisStep j))
      = 2 * (Real.cos (gridAngle k j) : ℂ) := by
    rw [charBasis k j h1L]
    change Complex.exp _ + (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (Complex.I * (gridAngle k j : ℂ)) = -(gridAngle k j : ℂ) * Complex.I := by simp; ring
    rw [hc, mul_comm Complex.I, ← Complex.two_cos, ← Complex.ofReal_cos]
  change (∑ y, (-(∑ j : Fin d,
    ((if y = x + basisStep j then 1 else 0 : ℂ) +
     (if y = x - basisStep j then 1 else 0 : ℂ)))) * character k y) = _
  simp_rw [neg_mul, Finset.sum_mul, add_mul]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  have hi (j : Fin d) : (∑ y : Torus d L,
      ((if y = x + basisStep j then 1 else 0 : ℂ) * character k y +
       (if y = x - basisStep j then 1 else 0 : ℂ) * character k y)) =
       character k x * (2 * (Real.cos (gridAngle k j) : ℂ)) := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [charAddX, charSubX, ← mul_add, hcos]
  simp_rw [hi]
  unfold dispersion
  push_cast
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The characters have unit modulus. -/
lemma charUnit (k x : Torus d L) : character k x * star (character k x) = 1 := by
  change character k x * (starRingEnd ℂ) (character k x) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, character_norm_eq]
  norm_num

lemma charNegK (k x : Torus d L) : character (-k) x = star (character k x) := by
  have hn : character k x ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ hn
  rw [← charAddK, add_neg_cancel, char_zero_freq, charUnit]

lemma charSubK (k l x : Torus d L) :
    character (k - l) x = character k x * star (character l x) := by
  rw [sub_eq_add_neg, charAddK, charNegK]

lemma charCross (k l x : Torus d L) :
    character k x * star (character l x) = star (character (l - k) x) := by
  rw [charSubK, star_mul, star_star, mul_comm]

/-- Fourier synthesis with the normalization of `gridAvg`. -/
def synthesis (s : Torus d L → ℂ) (x : Torus d L) : ℂ :=
  gridAvg (fun k => character k x * s k)

lemma fourier_synthesis (s : Torus d L → ℂ) (l : Torus d L) :
    fourier (synthesis s) l = s l := by
  have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := Torus d L)))
  unfold fourier synthesis gridAvg
  simp_rw [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hi (k : Torus d L) :
      (∑ x, character k x * s k * star (character l x)) =
      s k * (if k = l then (Fintype.card (Torus d L) : ℂ) else 0) := by
    rw [← orthRow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hi, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

lemma fourier_synthesis_mul (s g : Torus d L → ℂ) (l : Torus d L) :
    fourier (fun x => synthesis s x * g x) l =
      gridAvg (fun k => s k * fourier g (l - k)) := by
  unfold fourier synthesis gridAvg
  simp_rw [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← charCross]
  ring

lemma fourier_circulant (m v : Torus d L → ℂ) (k : Torus d L) :
    fourier ((circulant m).mulVec v) k = fourier m k * fourier v k := by
  have hr : fourier m k * fourier v k =
      ∑ y : Torus d L, ∑ x : Torus d L,
        m x * v y * star (character k x) * star (character k y) := by
    unfold fourier
    rw [Fintype.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hr]
  unfold fourier Matrix.mulVec dotProduct circulant
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Equiv.sum_comp (Equiv.addRight y)]
  change (∑ x : Torus d L, m ((x + y) - y) * v y * star (character k (x + y))) = _
  apply Finset.sum_congr rfl
  intro x _
  simp only [add_sub_cancel_right, charAddX, star_mul]
  ring

lemma row_parseval (m : Torus d L → ℂ) (x : Torus d L) :
    (∑ y, ‖circulant m x y‖ ^ 2) = gridAvgReal (fun k => ‖fourier m k‖ ^ 2) := by
  rw [← parseval]
  unfold circulant normSq
  exact (Equiv.subLeft x).sum_comp (fun y => ‖m y‖ ^ 2)

lemma circulant_normSq (m v : Torus d L → ℂ) (B : ℝ)
    (hB : ∀ k, ‖fourier m k‖ ≤ B) :
    normSq ((circulant m).mulVec v) ≤ B ^ 2 * normSq v := by
  have hB0 : 0 ≤ B := (norm_nonneg (fourier m 0)).trans (hB 0)
  rw [parseval, parseval]
  unfold gridAvgReal
  rw [mul_left_comm (B ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [fourier_circulant, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (sq_le_sq₀ (norm_nonneg _) hB0 |>.mpr (hB k)) (sq_nonneg _)

lemma circulant_opNorm (m : Torus d L → ℂ) (B : ℝ)
    (hB : ∀ k, ‖fourier m k‖ ≤ B) : opNorm (circulant m) ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg (fourier m 0)).trans (hB 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hB0
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB0 (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Matrix.ofLp_toEuclideanCLM]
  exact circulant_normSq m v.ofLp B hB

lemma freeGreen_synthesis (z : ℂ) (x : Torus d L) :
    freeGreen z x 0 = synthesis (fun k => ((dispersion (gridAngle k) : ℂ) - z)⁻¹) x := by
  simp only [freeGreen, sub_zero, synthesis]

lemma freeGreen_fourier (z : ℂ) (k : Torus d L) :
    fourier (fun x : Torus d L => freeGreen z x 0) k =
      ((dispersion (gridAngle k) : ℂ) - z)⁻¹ := by
  simp_rw [freeGreen_synthesis]
  exact fourier_synthesis _ _

lemma freeGreen_square (z : ℂ) (k : Torus d L) :
    fourier (fun x : Torus d L => freeGreen z x 0 ^ 2) k =
      gridAvg (fun l => ((dispersion (gridAngle l) : ℂ) - z)⁻¹ *
        ((dispersion (gridAngle (k - l)) : ℂ) - z)⁻¹) := by
  simp only [pow_two]
  simp_rw [freeGreen_synthesis]
  rw [fourier_synthesis_mul]
  simp_rw [fourier_synthesis]

lemma matrix_synthesis (A : Matrix (Torus d L) (Torus d L) ℂ)
    (s : Torus d L → ℂ) (x y : Torus d L) :
    (A * Matrix.of (fun w y => synthesis s (w - y))) x y =
      gridAvg (fun k => (A.mulVec (fun w => character k w)) x *
        star (character k y) * s k) := by
  change (∑ w, A x w * synthesis s (w - y)) = _
  unfold synthesis gridAvg
  simp_rw [charSubX]
  have hi (w : Torus d L) :
      A x w * ((Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, character k w * star (character k y) * s k) =
      (Fintype.card (Torus d L) : ℂ)⁻¹ *
        ∑ k, (A x w * character k w) * star (character k y) * s k := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]

lemma freeGreen_inverse (z : ℂ)
    (hz : ∀ k : Torus d L, (dispersion (gridAngle k) : ℂ) ≠ z) (hL : 4 ≤ L) :
    twoSidedInverse (freeHopping - z • (1 : Matrix (Torus d L) (Torus d L) ℂ))
      (freeGreen z) := by
  have he (k x : Torus d L) :
      ((freeHopping - z • (1 : Matrix (Torus d L) (Torus d L) ℂ)).mulVec
        (fun w => character k w)) x =
      ((dispersion (gridAngle k) : ℂ) - z) * character k x := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change (freeHopping.mulVec (fun w => character k w)) x - z * character k x = _
    rw [hoppingEigen k x hL]
    ring
  have hleft : (freeHopping - z • (1 : Matrix (Torus d L) (Torus d L) ℂ)) *
      freeGreen z = 1 := by
    ext x y
    have hG : freeGreen (d := d) (L := L) z =
        Matrix.of (fun (w y : Torus d L) => synthesis
          (fun (k : Torus d L) => ((dispersion (gridAngle k) : ℂ) - z)⁻¹) (w - y)) := rfl
    rw [hG, matrix_synthesis]
    simp_rw [he]
    have hi (k : Torus d L) :
        ((dispersion (gridAngle k) : ℂ) - z) * character k x * star (character k y) *
          ((dispersion (gridAngle k) : ℂ) - z)⁻¹ = character k x * star (character k y) := by
      have hn := sub_ne_zero.mpr (hz k)
      field_simp
    simp_rw [hi]
    unfold gridAvg
    have ho : (∑ k : Torus d L, character k x * star (character k y)) =
        if x = y then (Fintype.card (Torus d L) : ℂ) else 0 := by
      simpa only [mul_comm, eq_comm] using orthCol y x
    rw [ho]
    have hN : (Fintype.card (Torus d L) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos (α := Torus d L)))
    by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy, hN]
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

/-- All six frozen finite torus Fourier conclusions. -/
theorem torusFourier_proof : TorusFourierStatement := by
  intro d L inst hL
  refine ⟨?_, circulant_opNorm, row_parseval, ?_, gridAngle_add_exists, gridAngle_neg_exists⟩
  · intro z hz
    refine ⟨freeGreen_inverse z hz hL, ?_⟩
    intro x
    simp only [freeGreen, sub_self, char_zero, one_mul]
  · intro z _ k
    exact freeGreen_square z k

end AndersonAC.S3
