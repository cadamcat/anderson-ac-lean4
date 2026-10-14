import AndersonAC.S3.Definitions

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3

variable {d : ℕ}

/-! Helpers for lattice counting (paper Lemma 3.4, lines 198-210). -/

/-- Minimal cyclic coordinate distance. -/
def coordMin {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d) : ℕ :=
  min ((x j - y j).val) (L - (x j - y j).val)

/-- Sign bit distinguishing the two lifts of a minimal distance. -/
def coordBit {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d) : Fin 2 :=
  if ((x j - y j).val) = coordMin x y j then 0 else 1

theorem torusDistance_eq_sum {L : ℕ} [NeZero L] (x y : Torus d L) :
    torusDistance x y = ∑ j, coordMin x y j := rfl

theorem coordMin_le_sum {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d) :
    coordMin x y j ≤ torusDistance x y := by
  rw [torusDistance_eq_sum]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Every cyclic value is either the minimum or its complement. -/
theorem val_eq_min_or {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d) :
    (x j - y j).val = coordMin x y j ∨
      (x j - y j).val = L - coordMin x y j := by
  unfold coordMin
  set a := (x j - y j).val with ha
  have hle : a ≤ L := le_of_lt (lt_of_le_of_lt (le_refl a) (ZMod.val_lt _))
  -- `min a (L - a)` is one of the two
  rcases min_choice a (L - a) with h | h
  · left; rw [h]
  · right
    -- goal `a = L - min`, rewrite min
    rw [h]
    exact (Nat.sub_sub_self hle).symm

theorem val_of_bit_eq {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d)
    (h0 : coordBit x y j = 0) : (x j - y j).val = coordMin x y j := by
  unfold coordBit at h0
  split_ifs at h0 with h
  · exact h
  · simp at h0

theorem val_of_bit_ne {L : ℕ} [NeZero L] (x y : Torus d L) (j : Fin d)
    (h1 : coordBit x y j = 1) : (x j - y j).val = L - coordMin x y j := by
  unfold coordBit at h1
  split_ifs at h1 with h
  · simp at h1
  · rcases val_eq_min_or x y j with h' | h'
    · exact absurd h' h
    · exact h'

/-- Vals are recovered from (min, bit). -/
theorem val_eq_of_min_bit_eq {L : ℕ} [NeZero L] {x : Torus d L}
    {y₁ y₂ : Torus d L} {j : Fin d}
    (hmin : coordMin x y₁ j = coordMin x y₂ j)
    (hbit : coordBit x y₁ j = coordBit x y₂ j) :
    (x j - y₁ j).val = (x j - y₂ j).val := by
  by_cases h1 : (x j - y₁ j).val = coordMin x y₁ j
  · have hb1 : coordBit x y₁ j = 0 := by simp [coordBit, h1]
    rw [hb1] at hbit
    have h2eq : (x j - y₂ j).val = coordMin x y₂ j :=
      val_of_bit_eq x y₂ j hbit.symm
    calc (x j - y₁ j).val = coordMin x y₁ j := h1
      _ = coordMin x y₂ j := hmin
      _ = (x j - y₂ j).val := h2eq.symm
  · have hb1 : coordBit x y₁ j = 1 := by simp [coordBit, h1]
    rw [hb1] at hbit
    have e1 := val_of_bit_ne x y₁ j hb1
    have e2 := val_of_bit_ne x y₂ j hbit.symm
    rw [e1, e2, hmin]

theorem sub_eq_of_val_eq {L : ℕ} [NeZero L] {x : Torus d L}
    {y₁ y₂ : Torus d L}
    (h : ∀ j, (x j - y₁ j).val = (x j - y₂ j).val) : y₁ = y₂ := by
  have hsub : ∀ j, x j - y₁ j = x j - y₂ j := fun j =>
    ZMod.val_injective _ (h j)
  funext j
  have hj := hsub j
  have h1 : x j + (-(y₁ j)) = x j + (-(y₂ j)) := by
    simpa [sub_eq_add_neg] using hj
  have hneg : -(y₁ j) = -(y₂ j) := add_left_cancel_iff.mp h1
  exact neg_injective hneg

/-- Subtype of remaining coordinates after fixing one. -/
theorem card_erase_coord (i₀ : Fin d) :
    Fintype.card {j : Fin d // j ≠ i₀} = d - 1 := by
  have hequiv : {j : Fin d // j ≠ i₀} ≃ ↥(Finset.univ.erase i₀) :=
    Equiv.subtypeEquivRight (fun j => by simp [Finset.mem_erase])
  rw [Fintype.card_congr hequiv, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ i₀),
    Finset.card_univ, Fintype.card_fin]

/-- Uniform bound `(1+2s)^k e^{-s} ≤ 3^k (k+1)!` for `s ≥ 0`. -/
theorem pow_mul_exp_neg_le (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (1 + 2 * s) ^ k * Real.exp (-s)
      ≤ (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
  have hfact1 : (1 : ℝ) ≤ ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
    have h : 1 ≤ Nat.factorial (k + 1) :=
      Nat.succ_le_of_lt (Nat.factorial_pos _)
    exact_mod_cast h
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) _
  rcases le_total s 1 with hs1 | hs1
  · have hbase : (1 + 2 * s) ^ k ≤ (3 : ℝ) ^ k := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have hexp : Real.exp (-s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
    calc (1 + 2 * s) ^ k * Real.exp (-s)
        ≤ (3 : ℝ) ^ k * 1 :=
          mul_le_mul hbase hexp hexp_nonneg h3pos
      _ ≤ (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hfact1 h3pos
  · have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs1
    have hexp_le : s ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
        ≤ Real.exp s :=
      Real.pow_div_factorial_le_exp s hs (k + 1)
    have hfact_pos : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hspow_pos : (0 : ℝ) < s ^ (k + 1) := pow_pos hspos _
    have hexp_pos : (0 : ℝ) < Real.exp s := Real.exp_pos _
    have hexp_neg_le : Real.exp (-s)
        ≤ ((Nat.factorial (k + 1) : ℕ) : ℝ) / s ^ (k + 1) := by
      have h1 : s ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
          ≤ Real.exp s := hexp_le
      have hpos1 : (0 : ℝ) < s ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
        div_pos hspow_pos hfact_pos
      have h2 : (Real.exp s)⁻¹
          ≤ (s ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ))⁻¹ :=
        (inv_le_inv₀ hexp_pos hpos1).mpr h1
      rwa [← Real.exp_neg, inv_div] at h2
    have hbase : (1 + 2 * s) ^ k ≤ (3 * s) ^ k := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
    have h3s_nonneg : (0 : ℝ) ≤ (3 * s) ^ k := pow_nonneg (by linarith) _
    have hstep1 : (1 + 2 * s) ^ k * Real.exp (-s) ≤
        (3 * s) ^ k * (((Nat.factorial (k + 1) : ℕ) : ℝ) / s ^ (k + 1)) :=
      mul_le_mul hbase hexp_neg_le hexp_nonneg h3s_nonneg
    have hstep2 : (3 * s) ^ k * (((Nat.factorial (k + 1) : ℕ) : ℝ) / s ^ (k + 1))
        = (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) / s := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hspow_ne : s ^ (k + 1) ≠ 0 := pow_ne_zero _ hsne
      field_simp
      ring
    have hXnonneg : (0 : ℝ)
        ≤ (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
      mul_nonneg h3pos (zero_le_one.trans hfact1)
    have hs1' : (1 : ℝ) ≤ s := hs1
    calc (1 + 2 * s) ^ k * Real.exp (-s)
        ≤ (3 * s) ^ k * (((Nat.factorial (k + 1) : ℕ) : ℝ) / s ^ (k + 1)) :=
          hstep1
      _ = (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) / s := hstep2
      _ ≤ (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
          div_le_self hXnonneg hs1'

theorem lattice_shell_count_proof (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ (x : Torus d L) (r : ℕ),
        ((Finset.univ.filter (fun y => torusDistance x y = r)).card : ℝ) ≤
          C * (1 + (r : ℝ)) ^ (d - 1) := by
  refine ⟨(2 : ℝ) ^ d, pow_pos (by norm_num) _, fun L _ _ x r => ?_⟩
  have hd0 : 0 < d := by omega
  let i₀ : Fin d := ⟨0, hd0⟩
  set S := Finset.univ.filter (fun y : Torus d L => torusDistance x y = r) with hS
  have hmem : ∀ y ∈ S, torusDistance x y = r := fun y hy =>
    (Finset.mem_filter.mp hy).2
  have hsum_eq : ∀ y ∈ S, ∑ j, coordMin x y j = r := by
    intro y hy
    rw [← torusDistance_eq_sum]
    exact hmem y hy
  -- Target type for the injection
  set F1 := ({j : Fin d // j ≠ i₀} → Fin (r + 1)) with hF1
  set F2 := (Fin d → Fin 2) with hF2
  have hcard_le : S.card ≤ Fintype.card (F1 × F2) := by
    have h := Fintype.card_le_of_injective
      (fun s : ↥S => Prod.mk
        (((fun j => Fin.mk (coordMin x s.val j.val)
          (Nat.lt_succ_of_le (le_trans (coordMin_le_sum x s.val j.val)
            (le_of_eq (hmem s.val s.property))))) : F1))
        (((fun j => coordBit x s.val j)) : F2))
      (by
        intro a b hab
        obtain ⟨y₁, hy₁⟩ := a
        obtain ⟨y₂, hy₂⟩ := b
        have hfst := congrArg Prod.fst hab
        have hsnd := congrArg Prod.snd hab
        have hmin_rest : ∀ j : Fin d, j ≠ i₀ →
            coordMin x y₁ j = coordMin x y₂ j := by
          intro j hj
          have h := congrFun hfst ⟨j, hj⟩
          exact congrArg Fin.val h
        have hbit : ∀ j : Fin d, coordBit x y₁ j = coordBit x y₂ j :=
          fun j => congrFun hsnd j
        have hsum1 := hsum_eq y₁ hy₁
        have hsum2 := hsum_eq y₂ hy₂
        have herase_eq :
            Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₁ j) =
            Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₂ j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hmin_rest j (Finset.ne_of_mem_erase hj)
        have hadd1 : coordMin x y₁ i₀ +
            Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₁ j) = r :=
          (Finset.add_sum_erase Finset.univ (fun j => coordMin x y₁ j)
            (Finset.mem_univ i₀)).trans hsum1
        have hadd2 : coordMin x y₂ i₀ +
            Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₂ j) = r :=
          (Finset.add_sum_erase Finset.univ (fun j => coordMin x y₂ j)
            (Finset.mem_univ i₀)).trans hsum2
        have hmin0 : coordMin x y₁ i₀ = coordMin x y₂ i₀ := by
          have hr : coordMin x y₂ i₀ +
              Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₁ j) = r := by
            rw [herase_eq]
            exact hadd2
          have h : coordMin x y₁ i₀ +
              Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₁ j) =
              coordMin x y₂ i₀ +
              Finset.sum (Finset.univ.erase i₀) (fun j => coordMin x y₁ j) :=
            hadd1.trans hr.symm
          exact Nat.add_right_cancel h
        have hmin_all : ∀ j, coordMin x y₁ j = coordMin x y₂ j := by
          intro j
          by_cases hj : j = i₀
          · subst hj; exact hmin0
          · exact hmin_rest j hj
        have hval : ∀ j, (x j - y₁ j).val = (x j - y₂ j).val :=
          fun j => val_eq_of_min_bit_eq (hmin_all j) (hbit j)
        have hy : y₁ = y₂ := sub_eq_of_val_eq hval
        exact Subtype.ext hy)
    exact Fintype.card_coe S ▸ h
  have hcard_eq : Fintype.card (F1 × F2) = (r + 1) ^ (d - 1) * 2 ^ d := by
    rw [Fintype.card_prod]
    have h1 : Fintype.card F1 = (r + 1) ^ (d - 1) := by
      show Fintype.card ({j : Fin d // j ≠ i₀} → Fin (r + 1)) = _
      rw [Fintype.card_pi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [card_erase_coord i₀]
    have h2 : Fintype.card F2 = 2 ^ d := by
      show Fintype.card (Fin d → Fin 2) = _
      rw [Fintype.card_pi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]
    rw [h1, h2]
  have hnat : S.card ≤ (r + 1) ^ (d - 1) * 2 ^ d := by
    rw [← hcard_eq]; exact hcard_le
  -- cast to ℝ
  have hcast : (S.card : ℝ) ≤ ((r + 1) ^ (d - 1) * 2 ^ d : ℕ) := by
    exact Nat.cast_le.mpr hnat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at hcast
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hcast
  calc (S.card : ℝ) ≤ ((r : ℝ) + 1) ^ (d - 1) * (2 : ℝ) ^ d := hcast
    _ = (2 : ℝ) ^ d * (1 + (r : ℝ)) ^ (d - 1) := by ring

/-- Ball upper bound with explicit constant `2^d`. -/
theorem ball_upper_le {L : ℕ} [NeZero L] (x : Torus d L) (R : ℝ) (hR : 0 ≤ R) :
    (ballCard x R : ℝ) ≤ (2 : ℝ) ^ d * (1 + R) ^ d := by
  set K := ⌊R⌋₊ with hK
  have hKle : (K : ℝ) ≤ R := Nat.floor_le hR
  set B := Finset.univ.filter (fun y : Torus d L => (torusDistance x y : ℝ) ≤ R)
    with hB
  have hmemK : ∀ y ∈ B, torusDistance x y ≤ K := by
    intro y hy
    have hle : ((torusDistance x y : ℕ) : ℝ) ≤ R :=
      (Finset.mem_filter.mp hy).2
    exact Nat.le_floor hle
  have hcoord_le : ∀ y ∈ B, ∀ j : Fin d, coordMin x y j ≤ K := fun y hy j =>
    le_trans (coordMin_le_sum x y j) (hmemK y hy)
  set F1 := (Fin d → Fin (K + 1)) with hF1
  set F2 := (Fin d → Fin 2) with hF2
  have hcard_le : B.card ≤ Fintype.card (F1 × F2) := by
    have h := Fintype.card_le_of_injective
      (fun s : ↥B => Prod.mk
        (((fun j => Fin.mk (coordMin x s.val j)
          (Nat.lt_succ_of_le (hcoord_le s.val s.property j))) : F1))
        (((fun j => coordBit x s.val j)) : F2))
      (by
        intro a b hab
        obtain ⟨y₁, hy₁⟩ := a
        obtain ⟨y₂, hy₂⟩ := b
        have hfst := congrArg Prod.fst hab
        have hsnd := congrArg Prod.snd hab
        have hmin : ∀ j, coordMin x y₁ j = coordMin x y₂ j := by
          intro j
          have h := congrFun hfst j
          exact congrArg Fin.val h
        have hbit : ∀ j, coordBit x y₁ j = coordBit x y₂ j :=
          fun j => congrFun hsnd j
        have hval : ∀ j, (x j - y₁ j).val = (x j - y₂ j).val :=
          fun j => val_eq_of_min_bit_eq (hmin j) (hbit j)
        exact Subtype.ext (sub_eq_of_val_eq hval))
    exact Fintype.card_coe B ▸ h
  have hcard_eq : Fintype.card (F1 × F2) = (K + 1) ^ d * 2 ^ d := by
    rw [Fintype.card_prod]
    have h1 : Fintype.card F1 = (K + 1) ^ d := by
      show Fintype.card (Fin d → Fin (K + 1)) = _
      rw [Fintype.card_pi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : Fintype.card F2 = 2 ^ d := by
      show Fintype.card (Fin d → Fin 2) = _
      rw [Fintype.card_pi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]
    rw [h1, h2]
  have hnat : B.card ≤ (K + 1) ^ d * 2 ^ d := by
    rw [← hcard_eq]; exact hcard_le
  have hcast : (B.card : ℝ) ≤ ((K + 1) ^ d * 2 ^ d : ℕ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at hcast
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hcast
  have hK1_le : ((K : ℝ) + 1) ≤ 1 + R := by linarith
  have hK1_nonneg : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have hpow : ((K : ℝ) + 1) ^ d ≤ (1 + R) ^ d :=
    pow_le_pow_left₀ hK1_nonneg hK1_le d
  calc (B.card : ℝ) ≤ ((K : ℝ) + 1) ^ d * (2 : ℝ) ^ d := hcast
    _ ≤ (1 + R) ^ d * (2 : ℝ) ^ d := by
        apply mul_le_mul_of_nonneg_right hpow (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ d * (1 + R) ^ d := by ring

/-- Ball lower bound with explicit constant `1/d^d`. -/
theorem ball_lower_le {L : ℕ} [NeZero L] (hd : 3 ≤ d)
    (x : Torus d L) (R : ℝ) (hR1 : 1 ≤ R) (hRL : R ≤ (L : ℝ) / 4) :
    ((d ^ d : ℕ) : ℝ)⁻¹ * R ^ d ≤ (ballCard x R : ℝ) := by
  have hd0 : 0 < d := by omega
  have hdRpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
  have hdRne : (d : ℝ) ≠ 0 := ne_of_gt hdRpos
  set q := ⌊R / (d : ℝ)⌋₊ with hq
  have hRd_nonneg : (0 : ℝ) ≤ R / (d : ℝ) :=
    div_nonneg (le_trans zero_le_one hR1) hdRpos.le
  have hq_le : (q : ℝ) ≤ R / (d : ℝ) := Nat.floor_le hRd_nonneg
  have hq_lt_succ : R / (d : ℝ) < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLpos_nat : 0 < L := by
    have h : L ≠ 0 := NeZero.ne L
    omega
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hLpos_nat
  have hq_lt_L_nat : q < L := by
    have hR_lt_L : R < (L : ℝ) := lt_of_le_of_lt hRL (by linarith)
    have hRd_lt_L : R / (d : ℝ) < (L : ℝ) := by
      have h1 : R / (d : ℝ) ≤ R := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
          have h1d : 1 ≤ d := (by norm_num : 1 ≤ 3).trans hd
          exact_mod_cast h1d
        calc R / (d : ℝ) = R * ((d : ℝ))⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ R * 1 := by
              apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hR1)
              exact inv_le_one_of_one_le₀ hd1
          _ = R := by ring
      exact lt_of_le_of_lt h1 hR_lt_L
    have hqR : (q : ℝ) < (L : ℝ) := lt_of_le_of_lt hq_le hRd_lt_L
    exact Nat.cast_lt.mp hqR
  have hq_le_L4 : (q : ℝ) ≤ (L : ℝ) / 4 := by
    have h1 : R / (d : ℝ) ≤ (L : ℝ) / 4 := by
      have hRd_le_R : R / (d : ℝ) ≤ R := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
          have h1d : 1 ≤ d := (by norm_num : 1 ≤ 3).trans hd
          exact_mod_cast h1d
        calc R / (d : ℝ) = R * ((d : ℝ))⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ R * 1 := by
              apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hR1)
              exact inv_le_one_of_one_le₀ hd1
          _ = R := by ring
      exact le_trans hRd_le_R hRL
    exact le_trans hq_le h1
  -- Box embedding `t ↦ x - t`
  set B := Finset.univ.filter (fun y : Torus d L => (torusDistance x y : ℝ) ≤ R)
    with hB
  have hval_lt : ∀ (t : Fin d → Fin (q + 1)) (j : Fin d), (t j).val < L := fun t j =>
    lt_of_le_of_lt (Nat.lt_succ_iff.mp (Fin.is_lt _)) hq_lt_L_nat
  have htwo_le : ∀ (t : Fin d → Fin (q + 1)) (j : Fin d),
      (t j).val + (t j).val ≤ L := by
    intro t j
    have htq : (t j).val ≤ q := Nat.lt_succ_iff.mp (Fin.is_lt _)
    have htR : ((t j).val : ℝ) ≤ (L : ℝ) / 4 := by
      have h1 : ((t j).val : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr htq
      exact le_trans h1 hq_le_L4
    have h2 : 2 * ((t j).val : ℝ) ≤ (L : ℝ) := by linarith
    have h2n : (t j).val + (t j).val ≤ L := by
      have hcast : (((t j).val + (t j).val : ℕ) : ℝ) ≤ (L : ℝ) := by
        push_cast
        linarith
      exact Nat.cast_le.mp hcast
    exact h2n
  have hmin_eq : ∀ (t : Fin d → Fin (q + 1)) (j : Fin d),
      coordMin x (fun i => x i - (((t i).val : ℕ) : ZMod L)) j = (t j).val := by
    intro t j
    have htv : (t j).val < L := hval_lt t j
    have hsub_eq : x j - (x j - (((t j).val : ℕ) : ZMod L))
        = (((t j).val : ℕ) : ZMod L) := sub_sub_self _ _
    have hval_eq : (x j - (fun i => x i - (((t i).val : ℕ) : ZMod L)) j).val
        = (t j).val := by
      have hj : (fun i => x i - (((t i).val : ℕ) : ZMod L)) j
          = x j - (((t j).val : ℕ) : ZMod L) := rfl
      rw [hj, hsub_eq]
      exact ZMod.val_natCast_of_lt htv
    unfold coordMin
    rw [hval_eq]
    have htle : (t j).val ≤ L - (t j).val := by
      have hleL : (t j).val ≤ L :=
        le_of_lt (lt_of_le_of_lt (Nat.le_refl _) htv)
      have hadd := htwo_le t j
      rwa [Nat.le_sub_iff_add_le hleL]
    exact Nat.min_eq_left htle
  have hsum_le_R : ∀ (t : Fin d → Fin (q + 1)),
      ((Finset.sum Finset.univ (fun j => (t j).val) : ℕ) : ℝ) ≤ R := by
    intro t
    have heach : ∀ j : Fin d, (t j).val ≤ q := fun j =>
      Nat.lt_succ_iff.mp (Fin.is_lt _)
    have hsum_nat : Finset.sum Finset.univ (fun j => (t j).val) ≤ d * q := by
      calc Finset.sum Finset.univ (fun j => (t j).val)
          ≤ Finset.sum Finset.univ (fun _ => q) :=
            Finset.sum_le_sum (fun j _ => heach j)
        _ = d * q := by
            simp [Finset.sum_const, Finset.card_univ]
    have hcast : ((Finset.sum Finset.univ (fun j => (t j).val) : ℕ) : ℝ)
        ≤ ((d * q : ℕ) : ℝ) := Nat.cast_le.mpr hsum_nat
    rw [Nat.cast_mul] at hcast
    have hdq : (d : ℝ) * (q : ℝ) ≤ R := by
      have h1 : (d : ℝ) * (q : ℝ) ≤ (d : ℝ) * (R / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hq_le hdRpos.le
      rwa [mul_div_cancel₀ _ hdRne] at h1
    exact le_trans hcast hdq
  have hmem_ball : ∀ (t : Fin d → Fin (q + 1)),
      (fun i => x i - (((t i).val : ℕ) : ZMod L)) ∈ B := by
    intro t
    rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hdist_eq : torusDistance x (fun i => x i - (((t i).val : ℕ) : ZMod L))
        = Finset.sum Finset.univ (fun j => (t j).val) := by
      rw [torusDistance_eq_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact hmin_eq t j
    rw [hdist_eq]
    exact hsum_le_R t
  have hcard_le : Fintype.card (Fin d → Fin (q + 1)) ≤ B.card := by
    have h := Fintype.card_le_of_injective
      (fun t : (Fin d → Fin (q + 1)) =>
        (⟨(fun i => x i - (((t i).val : ℕ) : ZMod L)), hmem_ball t⟩ : ↥B))
      (by
        intro t₁ t₂ hab
        have hval_eq : (fun i => x i - (((t₁ i).val : ℕ) : ZMod L))
            = (fun i => x i - (((t₂ i).val : ℕ) : ZMod L)) :=
          congrArg Subtype.val hab
        funext j
        have hj := congrFun hval_eq j
        have hcast_eq : (((t₁ j).val : ℕ) : ZMod L)
            = (((t₂ j).val : ℕ) : ZMod L) := by
          have h1 : x j + (-(((t₁ j).val : ℕ) : ZMod L))
              = x j + (-(((t₂ j).val : ℕ) : ZMod L)) := by
            simpa [sub_eq_add_neg] using hj
          have hneg := add_left_cancel_iff.mp h1
          have h2 : -(((t₁ j).val : ℕ) : ZMod L)
              = -(((t₂ j).val : ℕ) : ZMod L) := hneg
          exact neg_injective h2
        have h1 : (t₁ j).val = (t₂ j).val := by
          have e1 := ZMod.val_natCast_of_lt (hval_lt t₁ j)
          have e2 := ZMod.val_natCast_of_lt (hval_lt t₂ j)
          have hc := congrArg ZMod.val hcast_eq
          rwa [e1, e2] at hc
        exact Fin.ext h1)
    have hco := Fintype.card_coe B
    rw [hco] at h
    exact h
  have hcard_eq : Fintype.card (Fin d → Fin (q + 1)) = (q + 1) ^ d := by
    rw [Fintype.card_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnat : (q + 1) ^ d ≤ B.card := by
    rw [← hcard_eq]; exact hcard_le
  have hcast : (((q + 1) ^ d : ℕ) : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hcast
  simp only [Nat.cast_add, Nat.cast_one] at hcast
  have hRdiv_le : R / (d : ℝ) ≤ (q : ℝ) + 1 := le_of_lt hq_lt_succ
  have hR_le : R ≤ (d : ℝ) * ((q : ℝ) + 1) := by
    have := (div_le_iff₀ hdRpos).mp hRdiv_le
    linarith [this]
  have hd_pow_pos : (0 : ℝ) < (d : ℝ) ^ d := pow_pos hdRpos d
  have hq1_nonneg : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
  have hpow_le : (R / (d : ℝ)) ^ d ≤ ((q : ℝ) + 1) ^ d :=
    pow_le_pow_left₀ (div_nonneg (le_trans zero_le_one hR1) hdRpos.le)
      hRdiv_le d
  have hdiv_pow : (R / (d : ℝ)) ^ d = R ^ d / (d : ℝ) ^ d := div_pow _ _ _
  have hc_eq : ((d ^ d : ℕ) : ℝ) = (d : ℝ) ^ d := by
    rw [Nat.cast_pow]
  have hc_pos : (0 : ℝ) < ((d ^ d : ℕ) : ℝ) := by
    rw [hc_eq]; exact hd_pow_pos
  calc ((d ^ d : ℕ) : ℝ)⁻¹ * R ^ d
      = R ^ d / (d : ℝ) ^ d := by rw [hc_eq]; rw [div_eq_mul_inv, mul_comm]
    _ = (R / (d : ℝ)) ^ d := by rw [hdiv_pow]
    _ ≤ ((q : ℝ) + 1) ^ d := hpow_le
    _ ≤ (B.card : ℝ) := hcast

/-- Monotonicity of the moment constant in `k`. -/
theorem moment_M_mono {k d : ℕ} (hk : k ≤ d + 1) :
    (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ)
      ≤ (3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ) := by
  have h3 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) hk
  have hfact : ((Nat.factorial (k + 1) : ℕ) : ℝ)
      ≤ ((Nat.factorial (d + 2) : ℕ) : ℝ) := by
    have h : k + 1 ≤ d + 2 := by omega
    have hle := Nat.factorial_le h
    exact_mod_cast hle
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) _
  have hfact_pos : (0 : ℝ) ≤ ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  exact mul_le_mul h3 hfact hfact_pos (pow_nonneg (by norm_num) _)

/-- Pointwise polynomial-exponential bound. -/
theorem pointwise_poly_exp_le (d k : ℕ) (hk : k ≤ d + 1)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (r : ℕ) :
    ((1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ)))
      ≤ ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ))
        * ((u ^ k)⁻¹) * (Real.exp (-u / 2)) ^ r := by
  set s := u * (r : ℝ) / 2 with hs
  have hs_nonneg : (0 : ℝ) ≤ s := by
    rw [hs]
    positivity
  have hune : (u : ℝ) ≠ 0 := ne_of_gt hu
  have hr_eq : (r : ℝ) = 2 * s / u := by
    rw [eq_div_iff hune]
    rw [hs]
    ring
  have h1u : (1 : ℝ) ≤ 1 / u := by
    rw [le_div_iff₀ hu]
    simpa using hu1
  have h1r_le : (1 : ℝ) + (r : ℝ) ≤ (1 + 2 * s) / u := by
    have h : (1 : ℝ) + (r : ℝ) ≤ 1 / u + 2 * s / u := by
      have hrw : (r : ℝ) = 2 * s / u := hr_eq
      rw [hrw]
      linarith [h1u]
    rwa [← add_div] at h
  have hpow_le : (1 + (r : ℝ)) ^ k ≤ (1 + 2 * s) ^ k / u ^ k := by
    have hle : (1 : ℝ) + (r : ℝ) ≤ (1 + 2 * s) / u :=
      h1r_le
    have hnonneg : (0 : ℝ) ≤ 1 + (r : ℝ) := by positivity
    calc (1 + (r : ℝ)) ^ k ≤ ((1 + 2 * s) / u) ^ k :=
          pow_le_pow_left₀ hnonneg hle k
      _ = (1 + 2 * s) ^ k / u ^ k := div_pow _ _ _
  have hexp_eq : Real.exp (-u * (r : ℝ)) = Real.exp (-s) * Real.exp (-s) := by
    have h : -u * (r : ℝ) = -s + -s := by rw [hs]; ring
    rw [h, Real.exp_add]
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hMk : (1 + 2 * s) ^ k * Real.exp (-s)
      ≤ (3 : ℝ) ^ k * ((Nat.factorial (k + 1) : ℕ) : ℝ) :=
    pow_mul_exp_neg_le k s hs_nonneg
  have hMle := moment_M_mono (d := d) (k := k) hk
  have huk_pos : (0 : ℝ) < u ^ k := pow_pos hu k
  calc (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ))
      = (1 + (r : ℝ)) ^ k * (Real.exp (-s) * Real.exp (-s)) := by rw [hexp_eq]
    _ = ((1 + (r : ℝ)) ^ k * Real.exp (-s)) * Real.exp (-s) := by ring
    _ ≤ (((1 + 2 * s) ^ k / u ^ k) * Real.exp (-s)) * Real.exp (-s) := by
        apply mul_le_mul_of_nonneg_right _ hexp_nonneg
        exact mul_le_mul_of_nonneg_right hpow_le hexp_nonneg
    _ = (((1 + 2 * s) ^ k * Real.exp (-s)) / u ^ k) * Real.exp (-s) := by
        rw [div_mul_eq_mul_div]
    _ ≤ ((((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ)) / u ^ k))
        * Real.exp (-s) := by
        apply mul_le_mul_of_nonneg_right _ hexp_nonneg
        have hle : ((1 + 2 * s) ^ k * Real.exp (-s)) / u ^ k
            ≤ ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ)) / u ^ k :=
          div_le_div_of_nonneg_right (hMk.trans hMle) (pow_nonneg hu.le k)
        exact hle
    _ = ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ))
        * ((u ^ k)⁻¹) * Real.exp (-s) := by
        rw [div_eq_mul_inv, mul_assoc]
    _ = ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ))
        * ((u ^ k)⁻¹) * (Real.exp (-u / 2)) ^ r := by
        congr 1
        -- `exp(-s) = exp(-u/2)^r`
        have hs_eq : -s = (r : ℝ) * (-u / 2) := by rw [hs]; ring
        rw [hs_eq, Real.exp_nat_mul]

/-- Finite geometric sum with ratio `exp(-u/2)` is at most `4/u`. -/
theorem geom_sum_exp_le (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (N : ℕ) :
    Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r) ≤ 4 / u := by
  set ρ := Real.exp (-u / 2) with hρ
  have hρ_nonneg : (0 : ℝ) ≤ ρ := (Real.exp_pos _).le
  have hρ_lt : ρ < 1 := by
    rw [hρ]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum_le : Finset.sum (Finset.range N) (fun r => ρ ^ r) ≤ (1 - ρ)⁻¹ := by
    have hsumm : Summable (fun r : ℕ => ρ ^ r) :=
      summable_geometric_of_lt_one hρ_nonneg hρ_lt
    have hle := hsumm.sum_le_tsum (Finset.range N)
      (fun i _ => pow_nonneg hρ_nonneg _)
    rwa [tsum_geometric_of_lt_one hρ_nonneg hρ_lt] at hle
  have h1ρ : u / 4 ≤ 1 - ρ := by
    have hv : (0 : ℝ) ≤ u / 2 := by linarith
    have hv1 : u / 2 ≤ 1 := by linarith
    have hexp_le : Real.exp (-(u / 2)) ≤ 1 / (1 + u / 2) := by
      have h1 : (1 : ℝ) + u / 2 ≤ Real.exp (u / 2) := by
        have h := Real.add_one_le_exp (u / 2)
        linarith
      have hpos1 : (0 : ℝ) < 1 + u / 2 := by linarith
      have hpos2 : (0 : ℝ) < Real.exp (u / 2) := Real.exp_pos _
      have h2 : (Real.exp (u / 2))⁻¹ ≤ (1 + u / 2)⁻¹ :=
        (inv_le_inv₀ hpos2 hpos1).mpr h1
      have e1 : Real.exp (-(u / 2)) = (Real.exp (u / 2))⁻¹ := Real.exp_neg _
      have e2 : (1 : ℝ) / (1 + u / 2) = (1 + u / 2)⁻¹ := one_div _
      rw [e1, e2]
      exact h2
      -- `exp(-v) = (exp v)⁻¹`, `1/(1+v) = (1+v)⁻¹`
    have h2 : u / 2 / (1 + u / 2) ≤ 1 - ρ := by
      have hρ_eq : ρ = Real.exp (-(u / 2)) := by rw [hρ]; ring_nf
      rw [hρ_eq]
      have hpos1 : (0 : ℝ) < 1 + u / 2 := by linarith
      have h_eq : (1 : ℝ) - 1 / (1 + u / 2) = u / 2 / (1 + u / 2) := by
        field_simp
        ring
      calc u / 2 / (1 + u / 2) = 1 - 1 / (1 + u / 2) := h_eq.symm
        _ ≤ 1 - Real.exp (-(u / 2)) := by
            apply sub_le_sub_left hexp_le
    have h3 : u / 4 ≤ u / 2 / (1 + u / 2) := by
      have hpos1 : (0 : ℝ) < 1 + u / 2 := by linarith
      have h4 : u / 4 * (1 + u / 2) ≤ u / 2 := by
        have : u / 4 * (1 + u / 2) = u / 4 + u * u / 8 := by ring
        rw [this]
        have hu2 : u * u / 8 ≤ u / 4 := by
          have : u * u ≤ 2 * u := by
            calc u * u ≤ 1 * u := by
                    apply mul_le_mul_of_nonneg_right hu1 hu.le
              _ = u := by ring
              _ ≤ 2 * u := by linarith
          linarith
        linarith
      exact (le_div_iff₀ hpos1).mpr h4
      -- `u/4 ≤ (u/2)/(1+u/2) ↔ u/4*(1+u/2) ≤ u/2`
    exact le_trans h3 h2
  have hposρ : (0 : ℝ) < 1 - ρ := lt_of_lt_of_le (by positivity) h1ρ
  have hu4pos : (0 : ℝ) < u / 4 := by positivity
  calc Finset.sum (Finset.range N) (fun r => ρ ^ r)
      ≤ (1 - ρ)⁻¹ := hsum_le
    _ ≤ (u / 4)⁻¹ := (inv_le_inv₀ hposρ hu4pos).mpr h1ρ
    _ = 4 / u := by rw [inv_div]

/-- Exponential moment bound from the shell bound. -/
theorem moment_le {L : ℕ} [NeZero L] (hd : 3 ≤ d) (C_shell : ℝ)
    (hCpos : 0 < C_shell)
    (hshell : ∀ (x : Torus d L) (r : ℕ),
      ((Finset.univ.filter (fun y => torusDistance x y = r)).card : ℝ)
        ≤ C_shell * (1 + (r : ℝ)) ^ (d - 1))
    (x : Torus d L) (u : ℝ) (a : ℕ) (hu : 0 < u) (hu1 : u ≤ 1)
    (ha : a ∈ ({0, 2} : Set ℕ)) :
    exponentialMoment x u a
      ≤ (4 * C_shell * ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ)))
        * u ^ (-(d + a : ℤ)) := by
  have ha_or : a = 0 ∨ a = 2 := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  have ha_le : a ≤ 2 := by rcases ha_or with rfl | rfl <;> norm_num
  set k := (d - 1) + a with hk
  have hk_le : k ≤ d + 1 := by omega
  have hk1_eq : k + 1 = d + a := by omega
  have hune : u ≠ 0 := ne_of_gt hu
  have huk_pos : (0 : ℝ) < u ^ k := pow_pos hu k
  set M : ℝ := (3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ) with hM
  have hMpos : (0 : ℝ) < M := by
    rw [hM]
    apply mul_pos (pow_pos (by norm_num) _)
    exact Nat.cast_pos.mpr (Nat.factorial_pos _)
  -- Every distance is at most `d * L`
  have hdist_le : ∀ y : Torus d L, torusDistance x y ≤ d * L := by
    intro y
    rw [torusDistance_eq_sum]
    have heach : ∀ j : Fin d, coordMin x y j ≤ L := fun j =>
      le_trans (le_trans (Nat.min_le_left _ _) (Nat.le_refl _))
        (le_of_lt (ZMod.val_lt _))
    calc Finset.sum Finset.univ (fun j => coordMin x y j)
        ≤ Finset.sum Finset.univ (fun _ => L) :=
          Finset.sum_le_sum (fun j _ => heach j)
      _ = d * L := by simp [Finset.sum_const, Finset.card_univ]
  set N := d * L + 1 with hN
  have hmem_range : ∀ y : Torus d L, torusDistance x y ∈ Finset.range N := fun y =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hdist_le y))
  -- Fiber decomposition
  have hdecomp : ∑ y : Torus d L,
        ((torusDistance x y : ℝ) ^ a * Real.exp (-u * (torusDistance x y : ℝ)))
      = Finset.sum (Finset.range N) (fun r =>
          Finset.sum (Finset.univ.filter (fun y => torusDistance x y = r))
            (fun _ => ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ))))) := by
    have hmaps : ∀ y ∈ (Finset.univ : Finset (Torus d L)),
        torusDistance x y ∈ Finset.range N := fun y _ => hmem_range y
    have h := Finset.sum_fiberwise_of_maps_to hmaps
      (fun y : Torus d L =>
        ((torusDistance x y : ℝ) ^ a * Real.exp (-u * (torusDistance x y : ℝ))))
    -- `h : ∑ r in range N, ∑ y in filter (dist = r), g y = ∑ y in univ, g y`
    rw [← h]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro y hy
    have hr : torusDistance x y = r := (Finset.mem_filter.mp hy).2
    rw [hr]
  have hexp_def : exponentialMoment x u a
      = ∑ y : Torus d L,
        ((torusDistance x y : ℝ) ^ a * Real.exp (-u * (torusDistance x y : ℝ))) :=
    rfl
  rw [hexp_def, hdecomp]
  -- Each fiber is bounded by the shell count
  have hfiber_le : ∀ r ∈ Finset.range N,
      Finset.sum (Finset.univ.filter (fun y => torusDistance x y = r))
        (fun _ => ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ))))
      ≤ C_shell * (((1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ)))) := by
    intro r _
    have hcard := hshell x r
    have hnonneg : (0 : ℝ) ≤ (r : ℝ) ^ a * Real.exp (-u * (r : ℝ)) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
    have hsum_eq : Finset.sum (Finset.univ.filter (fun y => torusDistance x y = r))
          (fun _ => ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ))))
        = ((Finset.univ.filter (fun y => torusDistance x y = r)).card : ℝ)
          * ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum_eq]
    have hr_le : (r : ℝ) ^ a ≤ (1 + (r : ℝ)) ^ a :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_left zero_le_one) a
    have h1r_pow : (1 + (r : ℝ)) ^ (d - 1) * (1 + (r : ℝ)) ^ a
        = (1 + (r : ℝ)) ^ k := by
      rw [← pow_add, ← hk]
    calc ((Finset.univ.filter (fun y => torusDistance x y = r)).card : ℝ)
          * ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ)))
        ≤ (C_shell * (1 + (r : ℝ)) ^ (d - 1))
          * ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard hnonneg
      _ = C_shell * ((1 + (r : ℝ)) ^ (d - 1) * (r : ℝ) ^ a)
          * Real.exp (-u * (r : ℝ)) := by ring
      _ ≤ C_shell * ((1 + (r : ℝ)) ^ (d - 1) * (1 + (r : ℝ)) ^ a)
          * Real.exp (-u * (r : ℝ)) := by
          have hX : (1 + (r : ℝ)) ^ (d - 1) * (r : ℝ) ^ a
              ≤ (1 + (r : ℝ)) ^ (d - 1) * (1 + (r : ℝ)) ^ a :=
            mul_le_mul_of_nonneg_left hr_le
              (pow_nonneg (by positivity) _)
          have hCX : C_shell * ((1 + (r : ℝ)) ^ (d - 1) * (r : ℝ) ^ a)
              ≤ C_shell * ((1 + (r : ℝ)) ^ (d - 1) * (1 + (r : ℝ)) ^ a) :=
            mul_le_mul_of_nonneg_left hX hCpos.le
          exact mul_le_mul_of_nonneg_right hCX (Real.exp_pos _).le
      _ = C_shell * (((1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ)))) := by
          rw [h1r_pow]; ring
  have hsum_le : Finset.sum (Finset.range N) (fun r =>
        Finset.sum (Finset.univ.filter (fun y => torusDistance x y = r))
          (fun _ => ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ)))))
      ≤ C_shell * Finset.sum (Finset.range N) (fun r =>
          (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r hr => hfiber_le r hr)
  have hpoint : ∀ r ∈ Finset.range N,
      (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ))
        ≤ M * ((u ^ k)⁻¹) * (Real.exp (-u / 2)) ^ r := by
    intro r _
    have h := pointwise_poly_exp_le d k hk_le u hu hu1 r
    rw [hM]
    exact h
  have hsum_point : Finset.sum (Finset.range N) (fun r =>
        (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ)))
      ≤ M * ((u ^ k)⁻¹) * Finset.sum (Finset.range N)
        (fun r => (Real.exp (-u / 2)) ^ r) := by
    have hle : Finset.sum (Finset.range N) (fun r =>
          (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ)))
        ≤ Finset.sum (Finset.range N) (fun r =>
          M * ((u ^ k)⁻¹) * (Real.exp (-u / 2)) ^ r) :=
      Finset.sum_le_sum (fun r hr => hpoint r hr)
    rwa [← Finset.mul_sum] at hle
    -- `∑ M*u⁻¹*ρ^r = M*u⁻¹*∑ ρ^r`
  have hgeom := geom_sum_exp_le u hu hu1 N
  have hC : C_shell * (M * ((u ^ k)⁻¹) *
      Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r))
      ≤ (4 * C_shell * M) * u ^ (-(d + a : ℤ)) := by
    have h1 : Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r)
        ≤ 4 / u := hgeom
    have huk_ne : (u ^ k) ≠ 0 := pow_ne_zero _ hune
    have h2 : M * ((u ^ k)⁻¹) *
        Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r)
        ≤ M * ((u ^ k)⁻¹) * (4 / u) := by
      apply mul_le_mul_of_nonneg_left h1
      apply mul_nonneg hMpos.le
      exact inv_nonneg.mpr (pow_nonneg hu.le _)
    have h3 : C_shell * (M * ((u ^ k)⁻¹) * (4 / u))
        = (4 * C_shell * M) * ((u ^ k)⁻¹ / u) := by ring
    have h4 : ((u ^ k)⁻¹) / u = u ^ (-(d + a : ℤ)) := by
      have hk_eq : (k + 1 : ℕ) = d + a := hk1_eq
      have hpow_succ : u ^ (k + 1) = u ^ k * u := pow_succ _ _
      have hzinv : u ^ (-(d + a : ℤ)) = ((u ^ (d + a : ℕ))⁻¹ : ℝ) := by
        rw [zpow_neg, ← Nat.cast_add, zpow_natCast]
      -- `(u^k)⁻¹ / u = (u^{k+1})⁻¹ = (u^{d+a})⁻¹`
      have h1 : ((u ^ k)⁻¹) / u = ((u ^ (k + 1) : ℝ))⁻¹ := by
        rw [hpow_succ]
        field_simp
      calc ((u ^ k)⁻¹) / u = ((u ^ (k + 1) : ℝ))⁻¹ := h1
        _ = ((u ^ (d + a : ℕ) : ℝ))⁻¹ := by rw [hk_eq]
        _ = u ^ (-(d + a : ℤ)) := hzinv.symm
    calc C_shell * (M * ((u ^ k)⁻¹) *
          Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r))
        ≤ C_shell * (M * ((u ^ k)⁻¹) * (4 / u)) := by
          apply mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (4 * C_shell * M) * (((u ^ k)⁻¹) / u) := h3
      _ = (4 * C_shell * M) * u ^ (-(d + a : ℤ)) := by rw [h4]
  calc Finset.sum (Finset.range N) (fun r =>
        Finset.sum (Finset.univ.filter (fun y => torusDistance x y = r))
          (fun _ => ((r : ℝ) ^ a * Real.exp (-u * (r : ℝ)))))
      ≤ C_shell * Finset.sum (Finset.range N) (fun r =>
          (1 + (r : ℝ)) ^ k * Real.exp (-u * (r : ℝ))) := hsum_le
    _ ≤ C_shell * (M * ((u ^ k)⁻¹) *
        Finset.sum (Finset.range N) (fun r => (Real.exp (-u / 2)) ^ r)) :=
        mul_le_mul_of_nonneg_left hsum_point hCpos.le
    _ ≤ (4 * C_shell * M) * u ^ (-(d + a : ℤ)) := hC

theorem lattice_counting_proof (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      (∀ (x : Torus d L) (R : ℝ), 0 ≤ R → (ballCard x R : ℝ) ≤ C * (1 + R) ^ d) ∧
      (∀ (x : Torus d L) (R : ℝ), 1 ≤ R → R ≤ (L : ℝ) / 4 →
        c * R ^ d ≤ (ballCard x R : ℝ)) ∧
      (∀ (x : Torus d L) (u : ℝ) (a : ℕ), 0 < u → u ≤ 1 → a ∈ ({0, 2} : Set ℕ) →
        exponentialMoment x u a ≤ C * u ^ (-(d + a : ℤ))) := by
  obtain ⟨C_shell, hCpos, hshell⟩ := lattice_shell_count_proof hd
  have hd0 : 0 < d := by omega
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hMpos : (0 : ℝ) < (3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ) := by
    apply mul_pos (pow_pos (by norm_num) _)
    exact Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hCMpos : (0 : ℝ) < 4 * C_shell *
      ((3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ)) := by
    apply mul_pos (mul_pos (by norm_num) hCpos) hMpos
  set M : ℝ := (3 : ℝ) ^ (d + 1) * ((Nat.factorial (d + 2) : ℕ) : ℝ) with hM
  set C : ℝ := (2 : ℝ) ^ d + 4 * C_shell * M with hC
  have hCpos' : (0 : ℝ) < C := by
    rw [hC]
    linarith [h2pos, hCMpos]
  have hd_pow_pos_nat : 0 < d ^ d := pow_pos hd0 _
  have hc_pos_real : (0 : ℝ) < ((d ^ d : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hd_pow_pos_nat
  set c : ℝ := ((d ^ d : ℕ) : ℝ)⁻¹ with hc
  have hcpos : (0 : ℝ) < c := inv_pos.mpr hc_pos_real
  refine ⟨c, C, hcpos, hCpos', fun L hinst hL => ⟨?upper, ?lower, ?moment⟩⟩
  · intro x R hR
    have h1 : (ballCard x R : ℝ) ≤ (2 : ℝ) ^ d * (1 + R) ^ d :=
      ball_upper_le x R hR
    have h2le : (2 : ℝ) ^ d ≤ C := by
      rw [hC]
      linarith [hCMpos.le]
    have hR1_nonneg : (0 : ℝ) ≤ (1 + R) ^ d :=
      pow_nonneg (by linarith) _
    calc (ballCard x R : ℝ) ≤ (2 : ℝ) ^ d * (1 + R) ^ d := h1
      _ ≤ C * (1 + R) ^ d := mul_le_mul_of_nonneg_right h2le hR1_nonneg
  · intro x R hR1 hRL
    have h := ball_lower_le hd x R hR1 hRL
    -- `ball_lower_le` gives `((d^d:ℕ):ℝ)⁻¹ * R^d ≤ ...`, which is `c * ...` by definition of `c`
    rw [hc]
    exact h
  · intro x u a hu hu1 ha
    have h := moment_le hd C_shell hCpos (hshell L hL) x u a hu hu1 ha
    have hMle : 4 * C_shell * M ≤ C := by
      rw [hC]
      linarith [h2pos.le]
    have hzpos : (0 : ℝ) ≤ u ^ (-(d + a : ℤ)) := (zpow_pos hu _).le
    calc exponentialMoment x u a
        ≤ (4 * C_shell * M) * u ^ (-(d + a : ℤ)) := h
      _ ≤ C * u ^ (-(d + a : ℤ)) :=
          mul_le_mul_of_nonneg_right hMle hzpos

end AndersonAC.S3
